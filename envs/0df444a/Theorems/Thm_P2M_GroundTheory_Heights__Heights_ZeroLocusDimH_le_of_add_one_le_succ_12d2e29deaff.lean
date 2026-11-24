-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_le_of_add_one_le_succ_12d2e29deaff
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_le_of_add_one_le_succ_12d2e29deaff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:28.226812+00:00
-- url     : https://prove2.me/theorems/bc17600f-14af-4799-a941-2e4374d62b51
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H le of add one le succ 12d2e29deaff: P2 M Ground Theory Heights  Heights Zero Locus Dim H le of add one le succ 12d2e29deaff
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H le of add one le succ 12d2e29deaff construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H le of add one le succ 12d2e29deaff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L42-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsZeroLocusDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHAlg
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeOfAddOneLeSucc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PZeroLocusDimH
import Theorems.Thm_UpperTheory_Reformulated_B_Qn14_le_of_add_one_le_succ

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

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_le_of_add_one_le_succ_12d2e29deaff {a : WithBot ℕ∞} {k : ℕ} (h : a + 1 ≤ ((k + 1 : ℕ) : WithBot ℕ∞)) :
    a ≤ (k : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«le_of_add_one_le_succ» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_le_of_add_one_le_succ_12d2e29deaff
