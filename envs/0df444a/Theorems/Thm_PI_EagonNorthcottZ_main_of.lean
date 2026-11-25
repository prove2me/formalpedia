-- Prove2me | Theorems.Thm_PI_EagonNorthcottZ_main_of
-- name    : PI.EagonNorthcottZ.main_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:57.680015+00:00
-- url     : https://prove2.me/theorems/a67411d5-8acf-50df-82b2-8af03fdd6875
-- title:
--   Eagon Northcott Z: main of
-- statement:
--   The Eagon Northcott Z construction uses the main of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/EagonNorthcottExactOf.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/EagonNorthcottIntegral/EagonNorthcottExactOf.lean#L10-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_ExactSecondDegreeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EagonNorthcottIntegral_EagonNorthcottExactOf
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

theorem PI.EagonNorthcottZ.main_of (hA : Anti) (hS : Sq) (hL : KLin) (hG : GrLin) (hGX : GrX) (hGY : GrY) (hX : ExX) (hY : ExY) (hYz : ExYz) :
    Main := by sorry
