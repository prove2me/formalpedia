-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_NTA_decomp
-- name    : PI.TwistedEisensteinNonvanishing.W.NTA.decomp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:37:11.638997+00:00
-- url     : https://prove2.me/theorems/80bee82b-2e99-4432-a3e4-cc528afb6f6c
-- title:
--   NTA: decomp
-- statement:
--   The NTA construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L194-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/IntegralApproximationByInteger.lean#L194-L227

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_UnitCongruentToInteger
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedNormLattice_UniformContinuityGaloisGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IntegralApproximationByInteger
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
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open PI.TwistedEisensteinNonvanishing.W.NTA
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem PI.TwistedEisensteinNonvanishing.W.NTA.decomp (hp : (Ideal.absNorm P.asIdeal).Prime) (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2)
    {α : 𝓞 E} (hα : α ≠ 0) : ∃ (k : ℕ) (u : E), algebraMap (𝓞 E) E α = (qOf P : E) ^ k * u ∧ u ≠ 0 ∧
      IntAt P u ∧ IntAt P u⁻¹ := by sorry
