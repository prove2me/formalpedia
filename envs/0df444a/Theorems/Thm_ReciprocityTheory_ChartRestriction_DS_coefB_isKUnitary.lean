-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefB_isKUnitary
-- name    : ReciprocityTheory.ChartRestriction.DS.coefB_isKUnitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:09:56.971279+00:00
-- url     : https://prove2.me/theorems/ec6337dd-0b6c-440e-9b75-a9b212ccc5f0
-- title:
--   DS: coef B is KUnitary
-- statement:
--   The DS construction uses the coef B is KUnitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L145-L152

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_HidaSetting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_TensorV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasimirGapAtNoncompactWeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KUnitB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefAInnerEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CoefBTensSubKStable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D]

theorem ReciprocityTheory.ChartRestriction.DS.coefB_isKUnitary (dual : Bool) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ D}
    (hU : IsKUnitary ε E) : IsKUnitary ε (fun a b => coefTr (tensF dual E a b)) := by sorry
