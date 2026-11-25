-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_coefB_sum_ite_right
-- name    : ReciprocityTheory.ChartRestriction.DS.coefB_sum_ite_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:48.804287+00:00
-- url     : https://prove2.me/theorems/fa5eacbe-e0ca-50ea-8842-a147e2a58987
-- title:
--   DS: coef B sum ite right
-- statement:
--   The DS construction uses the coef B sum ite right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L129-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/CoefBTensSubKStable.lean#L129-L135

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

theorem ReciprocityTheory.ChartRestriction.DS.coefB_sum_ite_right (a : Fin n) (x : D) (v : Fin n → D) :
    ∑ c, inner ℂ (v c) (if c = a then x else 0) = inner ℂ (v a) x := by sorry
