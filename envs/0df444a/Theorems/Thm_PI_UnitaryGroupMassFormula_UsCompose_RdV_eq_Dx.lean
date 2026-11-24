-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_RdV_eq_Dx
-- name    : PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:50:19.252108+00:00
-- url     : https://prove2.me/theorems/5ebd163d-3036-4cc8-915e-ab55b76c99da
-- title:
--   Us Compose: Rd V eq Dx
-- statement:
--   The Us Compose construction uses the Rd V eq Dx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/Expand.lean#L72-L75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx {k r : ℕ} (X : Mat k r) (f : Mat k r → E) : RdV X f = Dx (false, X) f := by sorry
