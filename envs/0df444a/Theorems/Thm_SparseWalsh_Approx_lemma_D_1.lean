-- Prove2me | Theorems.Thm_SparseWalsh_Approx_lemma_D_1
-- name    : SparseWalsh.Approx.lemma_D_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:02:59.225202+00:00
-- url     : https://prove2.me/theorems/3e544fa6-6a86-429b-9189-636c5642eca6
-- title:
--   Lemma D.1 — frequency location by repetition: failure at most K/M + 64‖η‖²/(Mλ²) + p
-- statement:
--   Fix a real coefficient vector $c$ on $\mathbb F_2^d$ and a set $S\subseteq\operatorname{supp}(c)$ with $|S|\le K$. Let $\eta$ agree with $c$ outside $S$ and vanish on $S$. Let $B\in\mathbb F_2^{m\times d}$ have independent uniform entries, and put $M=2^m$. Let $0<p<1/2$. Let $A$ be a random exact locator with a fixed number $D\ge1$ of rows that decodes each allowed frequency correctly except with probability at most $p/2$. Draw $u=\lceil(32/9)\ln(2D/p)\rceil$ uniform base shifts $x_1,\dots,x_u$, with hash, locator and shifts independent.
--
--   For each allowed $a\in S$, with $\lambda=c(a)\ne0$, the repetition construction applied to bucket $Ba$ of the tables $H^c_{B,\cdot}$ fails to return $a$ with probability at most
--   $$\frac KM+\frac{64\|\eta\|_2^2}{M\lambda^2}+p .$$
--   Each bucket yields at most one candidate. For every outcome of $B$, the locator and the shifts, the construction reads its tables at a set $Q$ of at most $Mu(D+1)$ points fixed by these choices, and for every residual $c=\hat f-w$ its output depends on $f$ only through the values of $f$ on $Q$. The construction therefore uses at most $Mu(D+1)$ non-adaptive value queries.
--
--   This is the location guarantee of §5.1 for repetition. The peeling analysis (Lemma 5.2) applies it at every stage.
--
--   Differences from the source:
--
--   - generalization: allowed = satisfying the degree restriction, when imposed → an arbitrary predicate `allowed` (used in the locator guarantee and in the retention check); reason: the proof uses only that a is allowed and the locator guarantee on allowed frequencies; no restriction and |a| ≤ k are instances
--   - reading: the guarantee also holds conditional on earlier-stage history independent of the current randomness → the bound for every fixed c, S and locator law; reason: conditioning on such history fixes c, S, η and leaves the current hash, locator and shifts with their original laws, so the conditional bound is this bound at the fixed values
--   - reading: uses at most Mu(D+1) value queries → the tables read f only at a set Q with |Q| ≤ M·u·(D+1) fixed by B, the locator rows and the shifts, and the output for every residual f̂ − w depends on f only through f on Q; reason: tables built from Eq. (3) at the u(D+1) shifts x_t, x_t + y_j read exactly these points
--   - encoding: at most one candidate per bucket → the construction returns an Option (Cube d) for each bucket; reason: one candidate or none by type
--   - encoding: probability over independent B, locator and shifts; majority with sgn(0) = 1 and a fixed tie rule → the PMF bind of the uniform law on B, the locator law μ and the uniform law on the shifts; bit j = 1 iff strictly more than u/2 comparisons give 1 (ties give 0); the bound as ENNReal.ofReal; reason: same law; the paper allows any fixed tie rule
-- source:
--   Attias, Bshouty, Medvedev, Srebro, Efficient Non-Adaptive Sparse Fourier Learning on the Boolean Cube and Finite Abelian Groups, STOC 2027 submission (manuscript sha256 4cbf9075…), p. 41 (PDF p. 44), Lemma D.1; setting pp. 40-41 (App. D.2 preamble, Repetition)

import Mathlib
import Definitions.Def_SparseWalsh_Approx_Fourier
import Definitions.Def_SparseWalsh_Approx_Locators

open scoped BigOperators Matrix

namespace SparseWalsh.Approx

/-- **Lemma D.1** (Frequency location by repetition), p. 41 (PDF p. 44), in the setting of the
App. D.2 preamble (p. 40). Fix a real coefficient vector `c` and `S ⊆ supp(c)` with `|S| ≤ K`;
`η` agrees with `c` outside `S` and vanishes on `S`. `B ∈ F_2^{m×d}` has independent uniform
entries, `M = 2^m`. `0 < p < 1/2`; the exact locator (law `μ`) has a fixed number `D ≥ 1` of rows
and fails with probability at most `p/2` on each allowed frequency; `u = ⌈(32/9) ln(2D/p)⌉` base
shifts `x_1, …, x_u` are uniform; hash, locator and shifts are independent. Then for each allowed
`a ∈ S`, with `λ = c(a) ≠ 0`, the repetition construction fails to return `a` from bucket `Ba`
with probability at most `K/M + 64‖η‖₂²/(Mλ²) + p`. Each bucket yields at most one candidate (an
`Option`), and the construction uses at most `Mu(D + 1)` value queries: its tables are read at a
set `Q` of at most `Mu(D+1)` points fixed by `B`, the locator and the shifts, and for every
residual `c = f̂ − w` its output depends on `f` only through `f` on `Q`. -/
theorem lemma_D_1 {d m D u K : ℕ} (c : Cube d → ℝ) (S : Finset (Cube d))
    (allowed : Cube d → Prop) (p : ℝ) (μ : PMF (Locator d)) (hS : ∀ a ∈ S, c a ≠ 0)
    (hK : S.card ≤ K) (hp0 : 0 < p) (hp1 : p < 1 / 2) (hD : 1 ≤ D)
    (hrows : ∀ ℓ ∈ μ.support, ℓ.rows.length = D)
    (hloc : ∀ a, allowed a →
      μ.toOuterMeasure {ℓ | ℓ.dec (meas ℓ a) ≠ some a} ≤ ENNReal.ofReal (p / 2))
    (hu : u = ⌈(32 / 9 : ℝ) * Real.log (2 * D / p)⌉₊) :
    (∀ a ∈ S, allowed a →
      ((PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (ZMod 2))).bind fun B =>
        μ.bind fun ℓ => (PMF.uniformOfFintype (Fin u → Cube d)).map fun x => (B, ℓ, x)).toOuterMeasure
        {t | repLocate (coefBucket c t.1) t.1 t.2.1 t.2.2 allowed (t.1 *ᵥ a) ≠ some a} ≤
      ENNReal.ofReal ((K : ℝ) / 2 ^ m +
        64 * coefNormSq (fun b => if b ∈ S then 0 else c b) / (2 ^ m * c a ^ 2) + p)) ∧
    (∀ (B : Matrix (Fin m) (Fin d) (ZMod 2)) (ℓ : Locator d), ℓ.rows.length = D →
      ∀ x : Fin u → Cube d,
        let Q := tablePoints B (Finset.univ.biUnion fun t =>
          insert (x t) (ℓ.rows.toFinset.image fun y => x t + y))
        Q.card ≤ 2 ^ m * u * (D + 1) ∧
        ∀ f f' : Cube d → ℝ, (∀ z ∈ Q, f z = f' z) → ∀ (w : Cube d → ℝ) (v : Cube m),
          repLocate (coefBucket (hat f - w) B) B ℓ x allowed v =
            repLocate (coefBucket (hat f' - w) B) B ℓ x allowed v) := by sorry

end SparseWalsh.Approx
