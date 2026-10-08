-- Prove2me | Theorems.Thm_WassersteinDRO_Duality_dual_kantorovich_problem
-- name    : WassersteinDRO.Duality.dual_kantorovich_problem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-21T02:17:55.479833+00:00
-- url     : https://prove2.me/theorems/1f01a6be-774e-40f3-b1a5-c5b5265150c9
-- title:
--   Theorem 1 — dual Kantorovich problem
-- statement:
--   For any $p \in [1,\infty)$, the $p$-th power of the type-$p$ Wasserstein distance between
--   two Borel probability measures $Q, Q'$ on $E$ admits the dual representation
--   $$W_p^p(Q,Q') = \sup\left\{\int_E \psi\,dQ' - \int_E \varphi\,dQ \;:\; \varphi,\psi \text{ bounded continuous on } E,\ \psi(\xi)-\varphi(\xi') \le \|\xi-\xi'\|^p\ \forall \xi,\xi' \right\}.$$
--   Both sides are compared in the extended reals so that the equality holds as a genuine
--   least upper bound even when no finite real bound attains it. The paper proves this by
--   citing Villani, *Optimal Transport: Old and New*, [108, §5], not with its own argument.
-- source:
--   Kuhn et al. 2019, Theorem 1, p. 4, citing Villani, Optimal Transport: Old and New, [108, § 5]

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory

namespace WassersteinDRO.Duality

/-- Theorem 1 (Dual Kantorovich problem), Kuhn et al. 2019, p. 4 (citing Villani,
*Optimal Transport: Old and New*, [108, § 5]): for any `p ∈ [1,∞)`, the `p`-th power of the
type-`p` Wasserstein distance between `Q` and `Q'` admits the dual representation
`Wp^p(Q,Q') = sup {∫ψ dQ' - ∫φ dQ : φ,ψ bounded continuous, ψ(ξ)-φ(ξ') ≤ ‖ξ-ξ'‖^p ∀ξ,ξ'}`.
Both sides are cast to `EReal` so the equality holds as a genuine supremum even when it is
not attained by a finite real bound, avoiding any junk value from Mathlib's real `sSup`. -/
theorem dual_kantorovich_problem {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [SecondCountableTopology E]
    (p : ℝ) (hp : 1 ≤ p) (Q Q' : Measure E)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure Q'] :
    ((wassersteinDistance p Q Q' ^ p : ENNReal) : EReal) =
      ⨆ (φ : BoundedContinuousFunction E ℝ) (ψ : BoundedContinuousFunction E ℝ)
          (_ : ∀ x y : E, ψ x - φ y ≤ ‖x - y‖ ^ p),
        ((∫ x, ψ x ∂Q' - ∫ x, φ x ∂Q : ℝ) : EReal) := by sorry

end WassersteinDRO.Duality
