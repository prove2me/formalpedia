-- Prove2me | Theorems.Thm_StochApproxDyn_LimitSet_exists_attractor_of_mapsTo_closure
-- name    : StochApproxDyn.LimitSet.exists_attractor_of_mapsTo_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:19:56.156193+00:00
-- url     : https://prove2.me/theorems/e7a8bc7a-05a6-4c22-a29e-b4906f7d57ac
-- title:
--   Lemma 5.2 — a trapping region with compact closure contains an attractor
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$. Let $U\subset M$ be a nonempty open set with compact closure $\overline U$, and suppose that
--   $$\Phi_T(\overline U)\subset U\qquad\text{for some }T>0 .$$
--   Then there exists an attractor $A\subset U$ whose basin contains $\overline U$.
--
--   This lemma, due to Conley, converts a trapping region into an attractor. It is the step that links attractors to chain recurrence in Proposition 5.3.
--
--   **Formalization Note** The hypothesis $U\ne\emptyset$ is added: the source omits it, but for $U=\emptyset$ the hypotheses hold and no attractor (which is nonempty by definition) can lie in $U$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 22, Lemma 5.2

import Mathlib
import Definitions.Def_StochApproxDyn_LimitSet_Attractor

open scoped NNReal

namespace StochApproxDyn.LimitSet

/-- Lemma 5.2 (Benaïm 1999, p. 22): if `U ⊂ M` is a nonempty open set with compact closure and
`Φ_T(Ū) ⊂ U` for some `T > 0`, then there is an attractor `A ⊂ U` whose basin contains `Ū`. -/
theorem exists_attractor_of_mapsTo_closure {M : Type*} [MetricSpace M] (Φ : Flow ℝ≥0 M)
    (U : Set M) (hUo : IsOpen U) (hUne : U.Nonempty) (hUc : IsCompact (closure U))
    (T : ℝ≥0) (hT : 0 < T) (hTU : Φ T '' closure U ⊆ U) :
    ∃ A : Set M, IsAttractor Φ A ∧ A ⊆ U ∧ closure U ⊆ basin Φ A := by sorry

end StochApproxDyn.LimitSet
