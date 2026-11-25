-- Prove2me | Theorems.Thm_PI_TwNormLat_W_intAt_sub
-- name    : PI.TwNormLat.W.intAt_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:13.187182+00:00
-- url     : https://prove2.me/theorems/9b2e4545-00b9-4c06-9741-d241c93ccce0
-- title:
--   W: int At sub
-- statement:
--   The W construction uses the int At sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L51-L53

import Definitions.Def_Formalism_PeriodIntegrals_TwNormLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwNormLat PI.TwNormLat.W
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem PI.TwNormLat.W.intAt_sub {a b : E} (ha : IntAt P a) (hb : IntAt P b) : IntAt P (a - b) := by sorry
