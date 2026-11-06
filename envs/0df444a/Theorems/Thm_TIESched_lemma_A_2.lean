-- Prove2me | Theorems.Thm_TIESched_lemma_A_2
-- name    : TIESched.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:48:06.81892+00:00
-- url     : https://prove2.me/theorems/de8c69ab-9628-4e2d-941d-c8fb692eaa9f
-- title:
--   Lemma A.2 — smoothed derivative identity without measurability
-- statement:
--   Let $I$ be a compatible positive integration, $(x,u)$ a feasible, truthful, padding-invariant fractional mechanism family, $J$ a job set with $|J|\ge2$, $D=m|J|$, and $\kappa$ a nonnegative smooth compactly supported kernel on $\mathbb R^D$. For the zero-extended interactions $V^J_i$, $G^J_{ij}$ and the convolution (10), on all of $\mathbb R^D$,
--   $$\frac{\partial}{\partial p_{ij}}\big(V^J_i*_L\kappa\big)=-\big(G^J_{ij}*_L\kappa\big),\qquad \sum_{i=1}^m\frac{\partial}{\partial p_{ij}}\big(V^J_i*_L\kappa\big)=0.$$
--
--   Thus Lemma 5.11 remains valid with $I_D$ in place of integration.
--
--   **Formalization Note.** The partial derivative is the derivative along the own-coordinate line; the first identity asserts that this derivative exists.
--
--   Differences from the source:
--   - generalization: the functionals I_D of Lemma A.1 → any family I satisfying properties (1)–(5) of Lemma A.1; reason: the argument (pp.40–41) uses only these properties; it specializes to the functionals of Lemma A.1
--   - reading: padding-invariant (T_v defined with one chosen fresh label per job set) → invariance for every fresh label k ∉ S; reason: the proof of Lemma 5.7 (p.25) views a job k ∈ J as the padding job of S∖{k}, which needs invariance for that label; the family of Lemma 5.6 is relabeling-equivariant, so the choice is immaterial (p.24)
--   - encoding: rules x^S, π^S on ℝ^{m×S}_{≥0} with values in X(S) → total functions on ℝ^{m×S}, with feasibility a separate predicate on nonnegative reports; reason: a family on the orthant extends to such a total function, and the hypotheses read nonnegative reports only
--   - encoding: ℝ^D with D = m|J| → report matrices Fin m → J → ℝ, identified with Fin (m|J|) → ℝ by ofCoords in the order of p.40; reason: the same space with the same Lebesgue measure
--   - encoding: ∂/∂p_ij of V^J_i ∗_L κ → derivative of the line t ↦ value at p with p_ij replaced by t; HasDerivAt in the first identity, deriv in the second; reason: the first identity also asserts existence, which the smoothness claim of p.40 gives
-- source:
--   Wang, Xu, Zhang, Tight Analysis of Randomized Truthful Scheduling: An (m+1)/2 Lower Bound, arXiv:2611.05142 (artifact sha256 a89db2da…), Lemma A.2, pp.40–41

import Mathlib
import Definitions.Def_TIESched_PaddingInvariant
import Definitions.Def_TIESched_utilityInteraction
import Definitions.Def_TIESched_SatisfiesVanishingHyps
import Definitions.Def_TIESched_IsCompatibleIntegration
import Definitions.Def_TIESched_convL

set_option autoImplicit false

namespace TIESched

/-- **Lemma A.2 (Smoothed derivative identity without measurability)** (Wang, Xu, Zhang,
arXiv:2611.05142, Lemma A.2, pp.40–41). Let `I` be compatible positive integration (Lemma A.1), let
`(x, u)` be a padding-invariant truthful fractional mechanism family, and fix a job set `J` with
`|J| ≥ 2`, `D = m|J|`. For the zero-extended interactions `V^J_i`, `G^J_ij` and every nonnegative
smooth compactly supported kernel `κ`, the convolution (10), `(f ∗_L κ)(p) = I_D(s ↦ f(s)κ(p − s))`,
satisfies on all of `ℝ^D`
`∂/∂p_ij (V^J_i ∗_L κ) = −(G^J_ij ∗_L κ)` and `Σ_{i=1}^m ∂/∂p_ij (V^J_i ∗_L κ) = 0`.

**Formalization Note.** `∂/∂p_ij` is the derivative along the own-coordinate line `t ↦ p|_{p_ij = t}`
(`updEntry`); the first identity is stated as `HasDerivAt`, so the derivative exists. Smooth means
`C^∞` on `ℝ^{m×J}`. -/
theorem lemma_A_2 (m : ℕ) [NeZero m] (hm : 2 ≤ m) (I : (D : ℕ) → ((Fin D → ℝ) → ℝ) → ℝ)
    (hI : IsCompatibleIntegration I) (M : FracMech m) (hfeas : Feasible M.alloc)
    (htr : Truthful M) (hpad : PaddingInvariant M) (J : Finset ℕ) (hJ : 2 ≤ J.card)
    (κ : (Fin m → J → ℝ) → ℝ) (hκ0 : ∀ s, 0 ≤ κ s) (hκs : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hκc : HasCompactSupport κ) :
    (∀ (i : Fin m) (j : J) (p : Fin m → J → ℝ),
      HasDerivAt
        (fun t => convL I J (zeroExt (fun q => utilityInteraction M J q i)) κ (updEntry p i j t))
        (-convL I J (zeroExt (fun q => interaction M.alloc J q i j)) κ p) (p i j)) ∧
    ∀ (j : J) (p : Fin m → J → ℝ),
      ∑ i, deriv
        (fun t => convL I J (zeroExt (fun q => utilityInteraction M J q i)) κ (updEntry p i j t))
        (p i j) = 0 := by sorry

end TIESched
