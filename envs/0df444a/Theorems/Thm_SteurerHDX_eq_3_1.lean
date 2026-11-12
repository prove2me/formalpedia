-- Prove2me | Theorems.Thm_SteurerHDX_eq_3_1
-- name    : SteurerHDX.eq_3_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:33:23.11393+00:00
-- url     : https://prove2.me/theorems/025013fd-622e-442e-b63a-914c325c9294
-- title:
--   Eq. (3.1): the test function has Rayleigh quotient below $1/(\beta^2(\varepsilon d)^2)$
-- statement:
--   This is the key estimate inside the proof of Theorem 3.1.
--
--   Let $\mathcal X$ be a pure $d$-dimensional complex with $n=|\mathcal X(d)|\ge2$ facets, let $0<\beta<1$ and $0<\varepsilon<1$, and let $A,B\subseteq\mathcal X(d)$ be disjoint with $|A|,|B|\ge\beta n$ such that $|\sigma\cap\tau|<d(1-\varepsilon)$ for all $\sigma\in A$, $\tau\in B$. For $\delta>0$ let
--   $$f(\sigma)=\max\Bigl\{1+\delta-\frac{\mathrm{dist}(\sigma,A)}{\varepsilon\cdot d},0\Bigr\},$$
--   with $\mathrm{dist}$ the shortest-path distance in the support graph $G$ of the down-up walk. Then for all sufficiently small $\delta>0$,
--   $$\frac{\mathcal E(f,f)}{\mathrm{Var}(f)}<\frac{1}{\beta^2\cdot(\varepsilon\cdot d)^2},$$
--   where $\mathcal E$ and $\mathrm{Var}$ are the Dirichlet form and variance of the down-up walk $P_d^\vee$ (uniform stationary distribution).
--
--   With Lemma 2.1 this bounds the spectral gap of the down-up walk from above whenever two large sets of facets are far apart.
--
--   **Formalization Note** The inequality is written as $\mathcal E(f,f)\cdot\beta^2(\varepsilon d)^2<\mathrm{Var}(f)$. $\mathcal E$ is the published Dirichlet form `GibbsCongestion.dirichletForm` evaluated at the down-up walk and its (uniform) stationary distribution.
--
--   Differences from the source:
--   - reading: δ > 0 but arbitrarily close to 0 → there is δ₀ > 0 such that the bound holds for every δ ∈ (0, δ₀); reason: the page needs f = 0 on B, which holds once (1 + δ)εd ≤ ⌊εd⌋ + 1, i.e. for all small δ
--   - encoding: E(f, f)/Var(f) < 1/(β²(εd)²) → E(f, f) · β²(εd)² < Var(f); reason: equivalent since β²(εd)² > 0 and E(f, f) ≥ 0, which forces Var(f) > 0; avoids Lean's x/0 = 0
--   - encoding: the standing setting of Theorem 3.1 (a pure complex with n facets) → IsPure X d and 2 ≤ |X(d)|; reason: n ≥ 2 is implicit (A, B disjoint with |A|, |B| ≥ βn > 0); for n = 0 the quotient is 0/0
--   - encoding: dist(σ, A), the shortest path distance to A → the minimum over a ∈ A of SimpleGraph.edist in ℕ∞, with f(σ) = 0 when it is ∞; reason: same values: an unreachable facet has max{1 + δ − ∞, 0} = 0
-- source:
--   Ebrahimnejad–Oveis Gharan, High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture, arXiv:2606.00292, proof of Theorem 3.1, Eq. (3.1), p.5

import Mathlib
import Definitions.Def_SteurerHDX_IsPure
import Definitions.Def_SteurerHDX_downUp
import Definitions.Def_SteurerHDX_walk
import Definitions.Def_SteurerHDX_variance
import Definitions.Def_SteurerHDX_testFn
import Definitions.Def_GibbsCongestion_dirichletForm

namespace SteurerHDX

/-- **Eq. (3.1) (test-function bound).** Ebrahimnejad–Oveis Gharan, *High-Dimensional Expanders, the Sparsest Cut Problem, and Steurer's Conjecture*, arXiv:2606.00292, proof of Theorem 3.1, Eq. (3.1), p.5:
"Fix 0 < β < 1 and disjoint sets A, B ⊆ [n] with |A|, |B| ≥ βn. Suppose … that |σ ∩ τ| < d(1 − ε)
for every σ ∈ A and τ ∈ B for some 0 < ε < 1 … Define f : X(d) → ℝ≥0 as follows:
f(σ) = max{1 + δ − dist(σ, A)/(ε·d), 0} … where … δ > 0 but arbitrarily close to 0. We show that
E(f, f)/Var(f) < 1/(β²·(ε·d)²)  (3.1)."

**Formalization Note.** X is a pure d-dimensional complex with n = |X(d)| ≥ 2 facets (the setting
of Theorem 3.1); E and Var are those of the down-up walk P_d^∨ (uniform μ): E is the published
`GibbsCongestion.dirichletForm` with P = `walk (downUp X d)` and π = `statDist (downUp X d)`. "δ > 0 but
arbitrarily close to 0" is read as: for all sufficiently small δ > 0. The inequality is written
in product form E(f,f)·β²(εd)² < Var(f), which is equivalent to (3.1) and also asserts
Var(f) > 0. -/
theorem eq_3_1 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (d : ℕ)
    (hX : IsPure X d) (hcard : 2 ≤ (faces X d).card) (β ε : ℝ)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε0 : 0 < ε) (hε1 : ε < 1)
    (A B : Finset (faces X d)) (hAB : Disjoint A B)
    (hA : β * (faces X d).card ≤ A.card) (hB : β * (faces X d).card ≤ B.card)
    (hsep : ∀ σ ∈ A, ∀ τ ∈ B, (((σ.1 ∩ τ.1).card : ℕ) : ℝ) < d * (1 - ε)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      GibbsCongestion.dirichletForm (walk (downUp X d)) (statDist (downUp X d))
          (testFn X d A ε δ) (testFn X d A ε δ) * (β ^ 2 * (ε * d) ^ 2) <
        variance (downUp X d) (testFn X d A ε δ) := by sorry

end SteurerHDX
