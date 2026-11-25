-- Prove2me | Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_sg_qinv
-- name    : PI.TwistedEisensteinNonvanishing.W.sg_qinv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:01.70334+00:00
-- url     : https://prove2.me/theorems/2febd4ba-7d66-44bb-a8a2-53024cfb285b
-- title:
--   W: sg qinv
-- statement:
--   The W construction uses the sg qinv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L256-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedEisensteinCoset/WeightedSumScaling.lean#L256-L281

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

theorem PI.TwistedEisensteinNonvanishing.W.sg_qinv {a b : ℕ} {φ : E → K} (h : Good1 P a b φ) (f : ℕ) :
    Good1 P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) ∧
      Sg P a (b + f) (fun u => φ (u / (qOf P : E) ^ f)) = Sg P a b φ := by sorry
