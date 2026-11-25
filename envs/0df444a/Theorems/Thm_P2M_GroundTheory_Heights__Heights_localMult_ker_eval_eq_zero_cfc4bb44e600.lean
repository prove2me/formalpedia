-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_localMult_ker_eval_eq_zero_cfc4bb44e600
-- name    : P2M_GroundTheory_Heights__Heights_localMult_ker_eval_eq_zero_cfc4bb44e600
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:48:36.238299+00:00
-- url     : https://prove2.me/theorems/11fadbe8-9491-4376-b13f-bc2f0d2d2f92
-- title:
--   P2 M Ground Theory Heights  Heights local Mult ker eval eq zero cfc4bb44e600: P2 M Ground Theory Heights  Heights local Mult ker eval eq zero cfc4bb44e600
-- statement:
--   The P2 M Ground Theory Heights  Heights local Mult ker eval eq zero cfc4bb44e600 construction uses the P2 M Ground Theory Heights  Heights local Mult ker eval eq zero cfc4bb44e600 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveBranchLength.lean#L11-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveBranchLength.lean#L11-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveBranchLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveBranchLength
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
open MvPolynomial ComplexSets Filter Topology

theorem P2M_GroundTheory_Heights__Heights_localMult_ker_eval_eq_zero_cfc4bb44e600 {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∈ J) (hgq : eval q g ≠ 0) :
    localMult J (RingHom.ker (eval q)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«localMult_ker_eval_eq_zero» := P2M_GroundTheory_Heights__Heights_localMult_ker_eval_eq_zero_cfc4bb44e600
