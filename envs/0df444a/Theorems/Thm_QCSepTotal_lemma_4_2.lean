-- Prove2me | Theorems.Thm_QCSepTotal_lemma_4_2
-- name    : QCSepTotal.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:43:06.881183+00:00
-- url     : https://prove2.me/theorems/f8853c37-1d4d-4882-9726-e732475424b2
-- title:
--   Lemma 4.2 — under (7) and (8) some $(x,y)$ has $\Pr_{\hat u,\hat v}[\Delta(Q^{\hat u,\hat v}_{x,y},Q_{x,y})>6\cdot10^{-5}]<10^{-6}$
-- statement:
--   Let $F$ be a partial function on finite sets $X\times Y$ and $\mu$ a distribution supported on $\mathrm{dom}(F)$. Let $c\ge1$ and $b\ge40$, let the fixed-seed maps $E_\ell:\mathbb F_2^{4b}\to\mathbb F_2^b$ be linear and surjective with $(u,\ell)\mapsto E_\ell(u)$ a strong $(2b,10^{-12})$-seeded extractor, and let $\Pi$ be a randomized protocol on the inputs $(x,U)$, $(y,V)$ of $F_{\mathrm{tot}}$ with $CC(\Pi)<b$. Set $\delta=1/(10^{22}c)$ and consider the random experiment of Section 4.1. If assumptions (7) and (8) hold, then there is $(x,y)$ in the support of $XY$ such that
--   $$\Pr_{\hat u,\hat v\leftarrow U_b}\Bigl[\Delta\bigl(Q^{\hat u,\hat v}_{x,y},Q_{x,y}\bigr)>\tau\Bigr]<10^{-6},\qquad \tau=6\cdot10^{6}\sqrt{c\delta}=6\cdot10^{-5},$$
--   where $\hat u,\hat v$ are sampled independently and uniformly from $\mathbb F_2^b$.
--
--   This is the step where the extractor enters: fixing the certificate address $\ell=L(x,y)$ and the values $E_\ell(U), E_\ell(V)$ usually changes the transcript distribution very little.
--
--   **Formalization Note** The paper has $CC(\Pi)<R(F)\le n+1\le b$ and uses it only to get $2^{CC(\Pi)-2b}\le2^{-b}$ (p.11). The protocol need not compute anything. The probability over $(\hat u,\hat v)$ is a count divided by $2^{2b}$, and "in the support of $XY$" is "$\Pr[X=x,Y=y]>0$".
--
--   Differences from the source:
--   - generalization: inputs in {0,1}^n → arbitrary finite input types X, Y; reason: {0,1}^n is a finite type, so the statement specializes
--   - generalization: CC(Π) < R(F) ≤ n + 1 ≤ b → CC(Π) < b; reason: the proof uses only CC(Π) < b (p.11), which the printed chain implies
--   - generalization: Π a 1/3-error protocol for Ftot (setting of Section 4) → any randomized protocol on the inputs of Ftot; reason: the proof of Lemma 4.2 does not use correctness
--   - generalization: c = ⌈K_E log² b⌉ and the extractor of Lemma 2.3 with ε = 10⁻¹² → any c ≥ 1 and any E with linear surjective fixed-seed maps that is a strong (2b, 10⁻¹²)-seeded extractor; reason: these are the only properties used; the paper's choice is a special case
--   - encoding: Pr over û, v̂ ← U_b → the number of pairs (û, v̂) with the property divided by 2^{2b}; reason: uniform probability on a finite set
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Lemma 4.2, p.9 (eq. (9)); proved pp.10–13

import Mathlib
import Definitions.Def_QCSepTotal_IsStrongExtractor
import Definitions.Def_QCSepTotal_LookupExperiment

namespace QCSepTotal

/-- **Lemma 4.2** (F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.9; proved pp.10–13). In the setting of Section 4:
`µ` is a distribution supported on `dom(F)`, `c ≥ 1`, `b ≥ 40`, `E` has linear surjective
fixed-seed maps and is a strong `(2b, 10⁻¹²)`-seeded extractor, `Π` is a randomized protocol on
the inputs `(x, U)`, `(y, V)` of `Ftot` with `CC(Π) < b`, and `δ = 1/(10²² c)`. Under
assumptions (7) and (8) there exists `(x, y)` in the support of `XY` such that
`Pr_{û, v̂ ← U_b}[Δ(Q^{û,v̂}_{x,y}, Q_{x,y}) > τ] < 10⁻⁶` (9), where `τ = 6 · 10⁶ √(cδ) = 6 · 10⁻⁵`
and `û, v̂` are sampled independently.

**Formalization Note.** The paper has `CC(Π) < R(F) ≤ n + 1 ≤ b` (pp.7, 11), used only to get
`2^{CC(Π) − 2b} ≤ 2^{−b}`; the hypothesis `P.cost < b` is that consequence. `Π` need not compute
anything. The probability over `(û, v̂)` is a count over `F₂^b × F₂^b` divided by `2^{2b}`. -/
theorem lemma_4_2 {X Y : Type} [Fintype X] [Fintype Y] (F : PartialFn X Y) (μ : PMF (X × Y))
    (hμ : ∀ p ∈ μ.support, (F p.1 p.2).isSome) (c b : ℕ) (hc : 1 ≤ c) (hb : 40 ≤ b)
    (E : (Fin c → ZMod 2) → (Fin (4 * b) → ZMod 2) →ₗ[ZMod 2] (Fin b → ZMod 2))
    (hEsurj : ∀ ℓ, Function.Surjective (E ℓ))
    (hEext : IsStrongExtractor (fun u ℓ => E ℓ u) (2 * (b : ℝ)) (1 / 10 ^ 12))
    (P : RandProtocol ((Fin c → X) × (Fin (4 * b) → ZMod 2)) ((Fin c → Y) × (Fin (4 * b) → ZMod 2)))
    (hcost : P.cost < b) (h7 : Assumption7 F μ P (deltaC c)) (h8 : Assumption8 F μ P (deltaC c)) :
    ∃ (x : Fin c → X) (y : Fin c → Y),
      0 < prob (lookupLaw μ P) {ω | LookupSample.xs ω = x ∧ LookupSample.ys ω = y} ∧
      ((Finset.univ.filter fun uv : (Fin b → ZMod 2) × (Fin b → ZMod 2) =>
          6 / 10 ^ 5 < tv (Qhat F μ P E x y uv.1 uv.2) (Qxy μ P x y)).card : ℝ) / 2 ^ (2 * b)
        < 1 / 10 ^ 6 := by sorry

end QCSepTotal
