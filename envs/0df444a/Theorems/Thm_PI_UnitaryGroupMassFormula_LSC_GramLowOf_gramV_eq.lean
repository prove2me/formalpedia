-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LSC_GramLowOf_gramV_eq
-- name    : PI.UnitaryGroupMassFormula.LSC.GramLowOf.gramV_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:05.725535+00:00
-- url     : https://prove2.me/theorems/ee59eb28-a7a1-430c-b1eb-f919b1225fe1
-- title:
--   Gram Low Of: gram V eq
-- statement:
--   The Gram Low Of construction uses the gram V eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/GramLowOf.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeSizeContinuity/GramLowOf.lean#L11-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_LatSizeContOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeSizeContinuity_GramLowOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI.LatSizeCont
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LSC PI.UnitaryGroupMassFormula.LSC.GramLowOf

theorem PI.UnitaryGroupMassFormula.LSC.GramLowOf.gramV_eq (I : Formalism.MainNotions.S.AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) :
    Size.gramV I x v b =
      ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i)))ᴴ *
        ((Formalism.MainNotions.S.uMat (x.1 v)⁻¹ * (I.P v)⁻¹) * Matrix.of (fun i a => I.φ v (b a i))) := by sorry
