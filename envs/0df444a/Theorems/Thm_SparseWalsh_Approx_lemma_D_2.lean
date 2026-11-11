-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_D_2
-- name    : SparseWalsh.Approx.lemma_D_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:03:07.356962+00:00
-- url     : https://prove2.me/theorems/1dcd27e6-6ee6-430a-b917-a77ebe0ddded
-- title:
--   Lemma D.2 — frequency location by coding: failure at most K/M + 8‖η‖²/(βMλ²) + p
-- statement:
--   Fix a real coefficient vector $c$ on $\mathbb F_2^d$ and a set $S\subseteq\operatorname{supp}(c)$ with $|S|\le K$. Let $\eta$ agree with $c$ outside $S$ and vanish on $S$. Let $B\in\mathbb F_2^{m\times d}$ have independent uniform entries, and put $M=2^m$. Let $A$ be a random exact locator with $D$ rows that decodes each allowed frequency correctly except with probability at most $p$. Let $E:\mathbb F_2^D\to\mathbb F_2^P$ be an injective binary linear code whose decoder corrects every pattern of at most $\beta P$ errors, $0<\beta\le1$. Let the base shift $x$ be uniform, with hash, locator and shift independent. From bucket $v$ the construction forms the bits $(-1)^{z_j}=\operatorname{sgn}(H^c_{B,x}(v))\operatorname{sgn}(H^c_{B,x+y_j}(v))$ for the rows $y_j$ of $EA$, where $\operatorname{sgn}(0)=1$, decodes the code and then the locator, and retains the candidate if it hashes to $v$ and is allowed.
--
--   For every allowed $a\in S$, with $\lambda=c(a)\ne0$, the construction fails to return $a$ from bucket $Ba$ with probability at most
--   $$\frac KM+\frac{8\|\eta\|_2^2}{\beta M\lambda^2}+p .$$
--   Every bucket yields at most one retained candidate. The tables are read at a set of at most $M(P+1)$ points fixed by $B$, the locator, the code and $x$, and the output depends on $f$ only through these values. The construction therefore uses at most $M(P+1)$ value queries.
--
--   Differences from the source:
--
--   - generalization: allowed = satisfying the degree restriction, when imposed → an arbitrary predicate `allowed` (used in the locator guarantee and in the retention check); reason: the proof uses only that a is allowed and the locator guarantee on allowed frequencies; no restriction and |a| ≤ k are instances
--   - generalization: an injective binary linear code of constant rate → an injective binary linear code with no rate hypothesis; reason: neither the failure bound nor the query count M(P+1) uses the rate; every constant-rate code is an instance
--   - reading: the guarantee also holds conditional on earlier-stage history independent of the current randomness → the bound for every fixed c, S and locator law; reason: conditioning on such history fixes c, S, η and leaves the current hash, locator and shifts with their original laws, so the conditional bound is this bound at the fixed values
--   - reading: uses at most M(P+1) value queries → the tables read f only at a set Q with |Q| ≤ M·(P+1) fixed by B, the locator, the code and x, and the output for every residual f̂ − w depends on f only through f on Q; reason: tables built from Eq. (3) at the P+1 shifts x, x + (EA)_j read exactly these points
--   - encoding: at most one candidate per bucket → the construction returns an Option (Cube d) for each bucket; reason: one candidate or none by type
--   - encoding: probability over independent B, locator and x → the PMF bind of the uniform law on B, the locator law μ and the uniform law on x; the bound as ENNReal.ofReal; reason: same law
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 42 (PDF p. 45), Lemma D.2; setting pp. 40-41 (App. D.2 preamble, Coding, Eq. (10))

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma D.2** (Frequency location by coding), p. 42 (PDF p. 45), in the setting of the
App. D.2 preamble (p. 40) and the coding paragraph (p. 41). Fix a real coefficient vector `c` and
`S ⊆ supp(c)` with `|S| ≤ K`; `η` agrees with `c` outside `S` and vanishes on `S`. `B ∈ F_2^{m×d}`
has independent uniform entries, `M = 2^m`. The exact locator (law `μ`) has `D` rows and fails with
probability at most `p` on each allowed frequency; `E : F_2^D → F_2^P` is an injective binary
linear code whose decoder corrects every pattern of at most `βP` errors, `0 < β ≤ 1`; the base
shift `x` is uniform; hash, locator and shift are independent. Then for every allowed `a ∈ S`, with
`λ = c(a) ≠ 0`, the coding construction fails to return `a` from bucket `Ba` with probability at
most `K/M + 8‖η‖₂²/(βMλ²) + p`. Every bucket yields at most one retained candidate (an `Option`),
and the construction uses at most `M(P + 1)` value queries: its tables are read at a set `Q` of at
most `M(P+1)` points fixed by `B`, the locator, the code and `x`, and for every residual `c = f̂ − w`
its output depends on `f` only through `f` on `Q`. -/
theorem lemma_D_2 {d m D K : ℕ} (c : Cube d → ℝ) (S : Finset (Cube d))
    (allowed : Cube d → Prop) (p β : ℝ) (μ : PMF (Locator d)) (E : BinCode D)
    (hS : ∀ a ∈ S, c a ≠ 0) (hK : S.card ≤ K) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hrows : ∀ ℓ ∈ μ.support, ℓ.rows.length = D)
    (hloc : ∀ a, allowed a →
      μ.toOuterMeasure {ℓ | ℓ.dec (meas ℓ a) ≠ some a} ≤ ENNReal.ofReal p)
    (hinj : Function.Injective fun msg : Cube D => E.E *ᵥ msg) (hcorr : E.Corrects β) :
    (∀ a ∈ S, allowed a →
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod 2))).bind fun B =>
        μ.bind fun ℓ => (PMF.uniformOfFintype (Cube d)).map fun x => (B, ℓ, x)).toOuterMeasure
        {t | codeLocate (coefBucket c t.1) t.1 t.2.1 E t.2.2 allowed (t.1 *ᵥ a) ≠ some a} ≤
      ENNReal.ofReal ((K : ℝ) / 2 ^ m +
        8 * coefNormSq (fun b => if b ∈ S then 0 else c b) / (β * 2 ^ m * c a ^ 2) + p)) ∧
    (∀ (B : Matrix (Fin m) (Fin d) (ZMod 2)) (ℓ : Locator d), ℓ.rows.length = D →
      ∀ x : Cube d,
        let Q := tablePoints B (insert x ((Finset.univ : Finset (Fin E.P)).image fun j =>
          x + (E.E * locMatrix D ℓ) j))
        Q.card ≤ 2 ^ m * (E.P + 1) ∧
        ∀ f f' : Cube d → ℝ, (∀ z ∈ Q, f z = f' z) → ∀ (w : Cube d → ℝ) (v : Cube m),
          codeLocate (coefBucket (hat f - w) B) B ℓ E x allowed v =
            codeLocate (coefBucket (hat f' - w) B) B ℓ E x allowed v) := by sorry

end SparseWalsh.Approx
