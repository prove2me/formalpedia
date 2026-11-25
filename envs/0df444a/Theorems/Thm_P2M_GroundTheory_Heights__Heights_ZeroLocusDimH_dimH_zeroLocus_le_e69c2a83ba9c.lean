-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_zeroLocus_le_e69c2a83ba9c
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_zeroLocus_le_e69c2a83ba9c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:09.459435+00:00
-- url     : https://prove2.me/theorems/68dfda78-7913-4d50-ad53-8bb720746430
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H zero Locus le e69c2a83ba9c: P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H zero Locus le e69c2a83ba9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H zero Locus le e69c2a83ba9c construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H dim H zero Locus le e69c2a83ba9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L101-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L101-L126

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

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_zeroLocus_le_e69c2a83ba9c (d : ℕ) : ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d →
      dimH {x : Fin n → ℂ | ∀ q ∈ J, MvPolynomial.eval x q = 0} ≤ 2 * (d : ENNReal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«dimH_zeroLocus_le» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_dimH_zeroLocus_le_e69c2a83ba9c
