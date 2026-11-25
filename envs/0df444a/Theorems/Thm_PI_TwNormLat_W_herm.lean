-- Prove2me | Theorems.Thm_PI_TwNormLat_W_herm
-- name    : PI.TwNormLat.W.herm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:23:48.007845+00:00
-- url     : https://prove2.me/theorems/a68a1a14-028d-4844-b892-da6ddf1b85be
-- title:
--   W: herm
-- statement:
--   The W construction uses the herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/IdealForm.lean#L62-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedNormLattice/IdealForm.lean#L62-L121

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
variable {n : ℕ} (Mm : (Fin n → E) → Prop) (Madd : ∀ u v, Mm u → Mm v → Mm (u + v))
  (Msmul : ∀ t v, IntAt P t → Mm v → Mm (t • v)) (Mlam : ∀ v, (∀ l, IntAt P (v l)) → Mm v)
include Madd Msmul Mlam

theorem PI.TwNormLat.W.herm (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : ℕ)
    (Mbd : ∀ v, Mm v → ∀ l, IntAt P (qE P ^ j * v l)) :
    ∃ (K : Fin n → ℕ) (b : Fin n → Fin n → E), (∀ l, K l ≤ j) ∧ (∀ l, Mm (b l)) ∧
      (∀ l, b l l = (qE P ^ K l)⁻¹) ∧ UT b ∧
      ∀ v, Mm v → ∃ w : Fin n → E, (∀ l, IntAt P (w l)) ∧ v = ∑ l, w l • b l := by sorry
