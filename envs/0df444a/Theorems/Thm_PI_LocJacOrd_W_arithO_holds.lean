-- Prove2me | Theorems.Thm_PI_LocJacOrd_W_arithO_holds
-- name    : PI.LocJacOrd.W.arithO_holds
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:16:05.662849+00:00
-- url     : https://prove2.me/theorems/b8246da4-1b95-4845-820c-4703c16cbd15
-- title:
--   W: arith O holds
-- statement:
--   The W construction uses the arith O holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L155-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalJacobianOrder/AbsVNeZero.lean#L155-L164

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd

theorem PI.LocJacOrd.W.arithO_holds {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ArithO (F := F) v := by sorry
