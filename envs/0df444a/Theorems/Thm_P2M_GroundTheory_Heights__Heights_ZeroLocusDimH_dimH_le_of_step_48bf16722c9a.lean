-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_step_48bf16722c9a
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_step_48bf16722c9a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:05.079799+00:00
-- url     : https://prove2.me/theorems/2290f46e-1380-4d4c-9318-fa0f5f517927
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of step 48bf16722c9a: P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of step 48bf16722c9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of step 48bf16722c9a construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H le of step 48bf16722c9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L46-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L46-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_step_48bf16722c9a {n : ℕ} (d : ℕ)
    (hIH : ∀ J' : Ideal (MvPolynomial (Fin n) ℂ), ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') + 1 ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J', MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal))
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d) :
    dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«dimH_le_of_step» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_le_of_step_48bf16722c9a
