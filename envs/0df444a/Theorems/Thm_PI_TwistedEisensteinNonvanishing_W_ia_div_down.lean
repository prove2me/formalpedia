-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_ia_div_down
-- name    : PI.TwistedEisensteinNonvanishing.W.ia_div_down
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:29:52.6508+00:00
-- url     : https://prove2.me/theorems/afa8970f-d75f-424c-a5e8-8817b761904b
-- title:
--   W: ia div down
-- statement:
--   The W construction uses the ia div down property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IaDivDown.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IaDivDown.lean#L71-L78

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem PI.TwistedEisensteinNonvanishing.W.ia_div_down (hp : (Ideal.absNorm P.asIdeal).Prime) {b b' : ℕ} (hb : b' ≤ b) {x : E}
    (hx : IntAt P (x / (qOf P : E) ^ b)) : IntAt P (x / (qOf P : E) ^ b') := by sorry
