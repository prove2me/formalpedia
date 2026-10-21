-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_pureDuality
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_pureDuality
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:03:19.852662+00:00
-- url     : https://prove2.me/theorems/7c5d4c3b-9b32-4481-a3ec-421ae5e83e61
-- title:
--   Pure-state conditional entropy duality
-- statement:
--   Let rho_ABC be a pure normalized trace-class state on separable complex systems, and suppose H(C)<infinity. In natural-log units,
--   $$H(C|A)+H(C|B)=0.$$
--
--   This duality concerns the two conditional entropies of one pure tripartite state; it imposes no finiteness assumption on H(A) or H(B).
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 2, §1, unnumbered pure-state duality (6)

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

/-- Pure-state conditional-entropy duality (6), PDF p.2; H(C) is finite. -/
theorem conditionalEntropy_pureDuality {A B C : Type}
    [Countable A] [Countable B] [Countable C] (rho : PureState ((A × B) × C))
    (hC : homogeneousEntropy (traceFirst rho.val.coefficients) < ⊤) :
    finiteFirstConditionalEntropy (swapCoeff (dropMiddle (associateRight rho.val.coefficients))) +
      finiteFirstConditionalEntropy (swapCoeff (traceFirst (associateRight rho.val.coefficients))) = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
