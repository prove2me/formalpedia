-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_continuousOn
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_continuousOn
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:07:30.116557+00:00
-- url     : https://prove2.me/theorems/2e2a3678-1de6-4597-9fed-25c9b1b8e081
-- title:
--   Finite marginal entropy continuity transfers to conditional entropy
-- statement:
--   Let S be a subset of normalized trace-class states on separable complex systems AC, and suppose every rho in S has finite H(rho_C). Let S_C be the set of their C marginals. If the real-valued function sigma_C maps to H(sigma_C) is continuous on S_C in trace norm, then
--   $$\rho_{AC}\longmapsto H(C|A)_\rho\quad\text{is continuous on }S.$$
--
--   No finiteness or continuity assumption is imposed on H(A). This transfers local finite entropy continuity of the first register to conditional entropy; the finite-C domain is inherited from definition (2).
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 7, §2, Proposition 2: marginal-entropy continuity implies conditional-entropy continuity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- Proposition 2, PDF p.7. Entropy is continuous as a finite-valued function
on the C-marginal set. The finite-C domain is inherited from (2), PDF p.2;
no entropy assumption is imposed on A. State topology is the trace-norm topology. -/
theorem conditionalEntropy_continuousOn {A C : Type} [Countable A] [Countable C]
    (S : Set (State (A × C)))
    (hfinite : ∀ rho ∈ S, homogeneousEntropy (traceFirst rho.coefficients) < ⊤)
    (hcontinuous : ContinuousOn
      (fun omega : State C => (homogeneousEntropy omega.coefficients).toReal) (marginalSet S)) :
    ContinuousOn (fun rho : State (A × C) => finiteFirstConditionalEntropy (swapCoeff rho.coefficients)) S := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
