-- Prove2me | Theorems.Thm_PI_NcVal_OmVc1_gramMulTup_holds
-- name    : PI.NcVal.OmVc1.gramMulTup_holds
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:10:18.294645+00:00
-- url     : https://prove2.me/theorems/461a0754-4470-58f2-8783-a110af44aa42
-- title:
--   Om Vc1: gram Mul Tup holds
-- statement:
--   The Om Vc1 construction uses the gram Mul Tup holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/GramMulTupHolds.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ValuationLocalVolumes/GramMulTupHolds.lean#L30-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_GramMulTupHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc1
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale
open scoped TensorProduct

theorem PI.NcVal.OmVc1.gramMulTup_holds : GramMulTup := by sorry
