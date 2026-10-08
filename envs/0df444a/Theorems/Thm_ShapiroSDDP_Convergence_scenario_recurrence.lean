-- Prove2me | Theorems.Thm_ShapiroSDDP_Convergence_scenario_recurrence
-- name    : ShapiroSDDP.Convergence.scenario_recurrence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:35:23.910105+00:00
-- url     : https://prove2.me/theorems/87f92a5b-89e5-4528-8120-124216ec2bf0
-- title:
--   Proof of Proposition 3.1, p. 11 — w.p.1 every SAA scenario is drawn in the forward step for infinitely many iterations
-- statement:
--   Let the forward scenarios $X_{k,i}$, $k\in\mathbb N$, $i=1,\dots,M$ with $M\ge1$, be drawn by the subsampling procedure: mutually independent, each uniformly distributed on the $N$ scenarios of the SAA problem. Then with probability one, every scenario $s$ of the SAA problem is drawn at infinitely many iterations:
--   $$P\Big(\forall s\ \forall K\ \exists k\ge K\ \exists i:\ X_{k,i}=s\Big)=1 .$$
--
--   The paper's "the realization will happen in the forward step procedure for a sufficiently large number of iterations" is read as "at iterations beyond any given one", which is what the convergence argument needs after the approximations have stabilized.
--
--   **Formalization Note** The statement is "almost every sample point has the property"; the event is not required to be shown measurable.
-- source:
--   Shapiro, Analysis of Stochastic Dual Dynamic Programming Method, Optimization Online 2009/12/2509, p. 11, proof of Proposition 3.1

import Mathlib
import Definitions.Def_ShapiroSDDP_Convergence_Model
import Definitions.Def_ShapiroSDDP_Convergence_Sampling

open MeasureTheory

namespace ShapiroSDDP.Convergence

/-- Proof of Proposition 3.1, p. 11: under the subsampling procedure (i.i.d. uniform forward
scenarios, `M ≥ 1` per iteration), with probability one every scenario of the SAA problem is drawn
in the forward step at infinitely many iterations. -/
theorem scenario_recurrence (I : Instance) {M : ℕ} (hM : 0 < M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Fin M → Ω → Scen I)
    (hX : IsUniformIID I P X) :
    ∀ᵐ w ∂P, ∀ (s : Scen I) (K : ℕ), ∃ k, K ≤ k ∧ ∃ i, X k i w = s := by sorry

end ShapiroSDDP.Convergence
