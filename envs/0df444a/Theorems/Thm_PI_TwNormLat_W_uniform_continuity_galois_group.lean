-- Prove2me | Theorems.Thm_PI_TwNormLat_W_uniform_continuity_galois_group
-- name    : PI.TwNormLat.W.uniform_continuity_galois_group
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:28:43.873818+00:00
-- url     : https://prove2.me/theorems/a97e6281-9928-54ed-8ebe-fe6aa724c95b
-- title:
--   W: uniform continuity galois group
-- statement:
--   The W construction uses the uniform continuity galois group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L71-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L71-L89

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

theorem PI.TwNormLat.W.uniform_continuity_galois_group (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {r : 𝓞 E} (hr : r ∈ P.asIdeal) :
    ∃ s t : 𝓞 E, s ∉ P.asIdeal ∧ t * ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) = s * r := by sorry
