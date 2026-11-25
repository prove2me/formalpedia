-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_inx_X
-- name    : PI.EagonNorthcottZ.inx_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:49.501373+00:00
-- url     : https://prove2.me/theorems/9bbeb7f2-9b21-40f7-9599-faa4fa58b0bb
-- title:
--   Eagon Northcott Z: inx X
-- statement:
--   The Eagon Northcott Z construction uses the inx X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/CardFilterLtInsert.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/CardFilterLtInsert.lean#L27-L27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_DivisionPartitionTotal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_CardFilterLtInsert
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EagonNorthcottZ
open MvPolynomial PI.EagonNorthcott

theorem PI.EagonNorthcottZ.inx_X {D : ℕ} (i : Fin D) : inx (X i : S D) = xs i := by sorry
