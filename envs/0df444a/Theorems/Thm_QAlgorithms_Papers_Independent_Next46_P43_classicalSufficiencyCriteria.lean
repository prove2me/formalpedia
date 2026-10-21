-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P43_classicalSufficiencyCriteria
-- name    : QAlgorithms.Papers.Independent.Next46.P43.classicalSufficiencyCriteria
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:38:31.56026+00:00
-- url     : https://prove2.me/theorems/c83d5058-c2f6-4e9f-a75c-93cfa4d73096
-- title:
--   Proposition 1: three classical sufficiency criteria
-- statement:
--   Let $(P_\theta)_{\theta\in\Theta}$ be a nonempty family of probabilities on $(X,\mathcal A)$, dominated by a sigma-finite measure, and let $\mathcal A_0\subseteq\mathcal A$. Write $P_0\equiv\mathcal P$ when $P_0$ and the family have the same common null sets. The following three conditions are equivalent:
--
--   $$
--   \begin{aligned}
--   &\mathcal A_0\text{ is sufficient for }\mathcal P;\\
--   &\exists P_0\equiv\mathcal P:\ \text{each }dP_\theta/dP_0\text{ has an }\mathcal A_0\text{-measurable version};\\
--   &(X,\mathcal A,\mathcal P)\text{ and }(X,\mathcal A_0,\mathcal P|_{\mathcal A_0})\text{ are stochastically equivalent}.
--   \end{aligned}
--   $$
--
--   Here $P_0$ can be chosen a probability. Sufficiency uses one conditional-probability version for all parameters. Stochastic equivalence uses one normal positive unital operator on $L^\infty$ in each direction, preserving every family expectation. These characterize the information retained by restriction to a sub-sigma-algebra.
-- source:
--   Sufficiency in quantum statistical inference, arXiv:math-ph/0412093v1, PDF p. 5, Proposition 1: three classical sufficiency criteria

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P43

noncomputable section

open MeasureTheory Filter

open scoped ENNReal BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P43

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass IsDensity State tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (homogeneousEntropy generalizedRelativeEntropy traceFirst traceSecond)

/-- Proposition 1, PDF p.5: all three sufficiency criteria. A density must have
an m0-measurable version modulo P0-null sets; the selected total rnDeriv is
not required to be pointwise measurable for a smaller sigma-algebra. -/
theorem classicalSufficiencyCriteria
    {X Theta : Type*} [m : MeasurableSpace X] [Nonempty Theta]
    (P : Theta → Measure X) (hProb : ∀ theta, IsProbabilityMeasure (P theta))
    (mu : Measure X) [SigmaFinite mu] (hDom : ∀ theta, P theta ≪ mu)
    (m0 : MeasurableSpace X) (hSub : m0 ≤ m) :
    letI : MeasurableSpace X := m
    (@SufficientSigmaAlgebra X Theta m P m0 ↔
      ∃ P0 : @Measure X m, @IsProbabilityMeasure X m P0 ∧
        @SameNullSets X Theta m P0 P ∧
        ∀ theta, ∃ f : X → ℝ≥0∞, @Measurable X ℝ≥0∞ m0 _ f ∧
          f =ᵐ[P0] (P theta).rnDeriv P0) ∧
    (@SufficientSigmaAlgebra X Theta m P m0 ↔
      StochasticallyEquivalent m m0 P (fun theta => (P theta).trim hSub)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P43

end
