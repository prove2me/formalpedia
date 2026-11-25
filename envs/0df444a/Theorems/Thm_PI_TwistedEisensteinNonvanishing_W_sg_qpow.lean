-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_qpow
-- name    : PI.TwistedEisensteinNonvanishing.W.sg_qpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:29:37.74193+00:00
-- url     : https://prove2.me/theorems/32693702-8940-4f7a-a10d-af98739198c1
-- title:
--   W: sg qpow
-- statement:
--   The W construction uses the sg qpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L234-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L234-L254

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

theorem PI.TwistedEisensteinNonvanishing.W.sg_qpow {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) ∧
      Sg P (a + f) b (fun u => φ ((qOf P : E) ^ f * u)) = ((qOf P ^ f : ℕ) : K) * Sg P a b φ := by sorry
