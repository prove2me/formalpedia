-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_eval__aeval_a391fac762a4
-- name    : P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_eval__aeval_a391fac762a4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:44:20.792588+00:00
-- url     : https://prove2.me/theorems/b5f94a36-0f46-4cb3-bfb1-067eedb20639
-- title:
--   P2 M Ground Theory Heights  Heights Zero Locus Dim H eval eval  aeval a391fac762a4: P2 M Ground Theory Heights  Heights Zero Locus Dim H eval eval  aeval a391fac762a4
-- statement:
--   The P2 M Ground Theory Heights  Heights Zero Locus Dim H eval eval  aeval a391fac762a4 construction uses the P2 M Ground Theory Heights  Heights Zero Locus Dim H eval eval  aeval a391fac762a4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PZeroLocusDimH.lean#L16-L24

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

theorem P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_eval__aeval_a391fac762a4 {n s : ℕ} (π : Fin s → MvPolynomial (Fin n) ℂ)
    (Q : Polynomial (MvPolynomial (Fin s) ℂ)) (x : Fin n → ℂ) (i : Fin n) :
    MvPolynomial.eval x (Q.eval₂ (MvPolynomial.aeval π).toRingHom (X i)) =
      Polynomial.eval (x i) (Q.map (MvPolynomial.eval (paramMap π x))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ZeroLocusDimH».«eval_eval₂_aeval» := P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_eval_eval__aeval_a391fac762a4
