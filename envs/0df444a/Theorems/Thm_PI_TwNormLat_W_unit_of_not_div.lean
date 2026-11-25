-- Prove2me | Theorems.Thm_PI_TwNormLat_W_unit_of_not_div
-- name    : PI.TwNormLat.W.unit_of_not_div
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:28:51.105033+00:00
-- url     : https://prove2.me/theorems/9502b998-5051-4d10-b3cb-7ff49ce9f6d2
-- title:
--   W: unit of not div
-- statement:
--   The W construction uses the unit of not div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L91-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/UniformContinuityGaloisGroup.lean#L91-L117

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

theorem PI.TwNormLat.W.unit_of_not_div (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {y : E} (hy : IntAt P y)
    (hy' : ¬ IntAt P (y / qE P)) : IntAt P y⁻¹ := by sorry
