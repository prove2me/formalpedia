-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f
-- name    : P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:15:39.578148+00:00
-- url     : https://prove2.me/theorems/20e6abfc-8350-4878-b72a-0459188e97ca
-- title:
--   P2 M Ground Theory Heights  Heights Pointwise Lelong exists max c79fae73757f: P2 M Ground Theory Heights  Heights Pointwise Lelong exists max c79fae73757f
-- statement:
--   The P2 M Ground Theory Heights  Heights Pointwise Lelong exists max c79fae73757f construction uses the P2 M Ground Theory Heights  Heights Pointwise Lelong exists max c79fae73757f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L293-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PPointwiseLelong.lean#L293-L316

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f (hN : 1 ≤ N) (Q : MvPolynomial (Fin N) ℂ) :
    ∃ p : Fin N → ℂ, ∑ j, ‖p j‖ ^ 2 = 1 ∧
      ∀ z : Fin N → ℂ, ∑ j, ‖z j‖ ^ 2 = 1 → ‖eval z Q‖ ≤ ‖eval p Q‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointwiseLelong».«exists_max» := P2M_GroundTheory_Heights__Heights_PointwiseLelong_exists_max_c79fae73757f
