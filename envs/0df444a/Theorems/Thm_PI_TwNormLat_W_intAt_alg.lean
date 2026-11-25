-- Prove2me | Theorems.Thm_PI_TwNormLat_W_intAt_alg
-- name    : PI.TwNormLat.W.intAt_alg
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:47:49.45422+00:00
-- url     : https://prove2.me/theorems/65bbf1f8-9620-4c39-a132-ddf1fedb574b
-- title:
--   W: int At alg
-- statement:
--   The W construction uses the int At alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L17-L18

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

theorem PI.TwNormLat.W.intAt_alg (x : 𝓞 E) : IntAt P (algebraMap (𝓞 E) E x) := by sorry
