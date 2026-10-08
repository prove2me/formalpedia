-- Prove2me | Theorems.Thm_StochApproxDyn_Lyapunov_exists_attractor_of_mapsTo_closure
-- name    : StochApproxDyn.Lyapunov.exists_attractor_of_mapsTo_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:49:15.677455+00:00
-- url     : https://prove2.me/theorems/2b7c5574-27a5-402d-b46d-15c81194edc2
-- title:
--   Lemma 5.2 — a trapping region with compact closure contains an attractor
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$. Let $U\subset M$ be a nonempty open set with compact closure $\overline U$, and suppose that
--   $$\Phi_T(\overline U)\subset U\qquad\text{for some }T>0 .$$
--   Then there exists an attractor $A\subset U$ whose basin contains $\overline U$.
--
--   This lemma, due to Conley, produces attractors from trapping regions. In the proof of Proposition 6.4 it is applied to the restricted semiflow on an internally chain transitive set $L$, with $U$ a sublevel set of the Lyapounov function inside $L$.
--
--   **Formalization Note** The hypothesis that $U$ is nonempty is added: for $U=\emptyset$ the other hypotheses hold, but an attractor is nonempty by definition, so the page's statement needs it.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 22, Lemma 5.2

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.Lyapunov

/-- Lemma 5.2 (Benaïm 1999, p. 22): if `U ⊂ M` is a nonempty open set with compact closure and
`Φ_T(Ū) ⊂ U` for some `T > 0`, then there is an attractor `A ⊂ U` whose basin contains `Ū`. -/
theorem exists_attractor_of_mapsTo_closure {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, StochApproxDyn.LimitSet.IsAttractor Φ A ∧ A ⊆ U ∧ closure U ⊆ StochApproxDyn.LimitSet.basin Φ A := by sorry

end StochApproxDyn.Lyapunov
