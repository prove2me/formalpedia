-- Prove2me | Theorems.Thm_PI_TwNormLat_W_ideal_form
-- name    : PI.TwNormLat.W.ideal_form
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:31:14.19831+00:00
-- url     : https://prove2.me/theorems/55662589-0983-4863-aba3-a993b1fb099e
-- title:
--   W: ideal form
-- statement:
--   The W construction uses the ideal form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/IdealForm.lean#L12-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/IdealForm.lean#L12-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_CombinationEquivInvMemUnipotentFlagGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_IdealForm
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

theorem PI.TwNormLat.W.ideal_form (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ) (I : E → Prop) (hI1 : I 1)
    (hIm : ∀ t x, IntAt P t → I x → I (t * x)) (hIb : ∀ x, I x → IntAt P (qE P ^ j * x)) :
    ∃ K, K ≤ j ∧ I (qE P ^ K)⁻¹ ∧ ∀ x, I x → IntAt P (qE P ^ K * x) := by sorry
