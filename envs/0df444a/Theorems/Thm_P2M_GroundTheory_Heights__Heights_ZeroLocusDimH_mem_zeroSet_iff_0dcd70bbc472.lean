-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_mem_zeroSet_iff_0dcd70bbc472
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_mem_zeroSet_iff_0dcd70bbc472
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:48.569588+00:00
-- url     : https://prove2.me/theorems/d1dc3551-1006-45d9-81a8-2e48a60496f1
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H mem zero Set iff 0dcd70bbc472: P2 M Ground Theory Heights  Heights Zero Locus Dim H mem zero Set iff 0dcd70bbc472
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H mem zero Set iff 0dcd70bbc472 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H mem zero Set iff 0dcd70bbc472 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L26-L28

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

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_mem_zeroSet_iff_0dcd70bbc472 {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    (∀ q ∈ I, MvPolynomial.eval x q = 0) ↔ I ≤ RingHom.ker (MvPolynomial.eval x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«mem_zeroSet_iff» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_mem_zeroSet_iff_0dcd70bbc472
