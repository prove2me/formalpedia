-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_weighted_sum_scaling
-- name    : PI.TwistedEisensteinNonvanishing.W.weighted_sum_scaling
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:31:46.047472+00:00
-- url     : https://prove2.me/theorems/3af198f5-5494-4874-8c4f-c73cc24d0d28
-- title:
--   W: weighted sum scaling
-- statement:
--   The W construction uses the weighted sum scaling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L285-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L285-L315

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_IaDivDown
import Definitions.Def_Lemmata_PeriodicFunctions_PeriodicApplyMulAdd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumScaling
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
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)}
variable (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq
include hK

theorem PI.TwistedEisensteinNonvanishing.W.weighted_sum_scaling {d : E} (hd : d ≠ 0) (a b : ℕ) :
    ∃ a' b' : ℕ, ∀ φ : E → K, Good1 P a b φ →
      Good1 P a' b' (fun u => φ (d * u)) ∧ W1 P a' b' (fun u => φ (d * u)) = (qOf P : K) ^ vq P d * W1 P a b φ := by sorry
