-- Prove2me | Theorems.Thm_PI_QmSandwichWork_tm_entry_comm
-- name    : PI.QmSandwichWork.tm_entry_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:39:11.780576+00:00
-- url     : https://prove2.me/theorems/42d63c98-6741-4462-affb-3538079f71b4
-- title:
--   Qm Sandwich Work: tm entry comm
-- statement:
--   The Qm Sandwich Work construction uses the tm entry comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EntrywiseSandwichCommute/BlockEmbeddingMulEntrySwap.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_RttRelation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EntrywiseSandwichCommute_BlockEmbeddingMulEntrySwap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmSandwichWork
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W
variable {A : Type} [Ring A] [Algebra ℂ A]

theorem PI.QmSandwichWork.tm_entry_comm (Y : ℂ) {p c ci x : A} (hp : Commute p x) (hc : Commute c x)
    (hci : Commute ci x) (i j : Fin 2) : Commute (Tm Y p c ci i j) x := by sorry
