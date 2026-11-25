-- Prove2me | Theorems.Thm_PI_OmFibreUniq_W_SdChar_eq_one_of_pow_near
-- name    : PI.OmFibreUniq.W.SdChar.eq_one_of_pow_near
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:34.801487+00:00
-- url     : https://prove2.me/theorems/380fdf89-1cbd-58c5-bb0b-dfba78399acc
-- title:
--   Sd Char: eq one of pow near
-- statement:
--   The Sd Char construction uses the eq one of pow near property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExChar.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarFibreUniqueness/SdExChar.lean#L11-L60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdChar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain

theorem PI.OmFibreUniq.W.SdChar.eq_one_of_pow_near (w : ℂ) (hw : ‖w‖ = 1) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1) : w = 1 := by sorry
