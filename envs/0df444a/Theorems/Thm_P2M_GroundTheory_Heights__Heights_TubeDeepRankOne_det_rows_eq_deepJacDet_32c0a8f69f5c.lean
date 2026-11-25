-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_det_rows_eq_deepJacDet_32c0a8f69f5c
-- name    : P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_det_rows_eq_deepJacDet_32c0a8f69f5c
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:43:18.427331+00:00
-- url     : https://prove2.me/theorems/b8b4a7c5-8904-42aa-aeb1-143c549613d7
-- title:
--   P2 M Ground Theory Heights  Heights Tube Deep Rank One det rows eq deep Jac Det 32c0a8f69f5c: P2 M Ground Theory Heights  Heights Tube Deep Rank One det rows eq deep Jac Det 32c0a8f69f5c
-- statement:
--   The P2 M Ground Theory Heights  Heights Tube Deep Rank One det rows eq deep Jac Det 32c0a8f69f5c construction uses the P2 M Ground Theory Heights  Heights Tube Deep Rank One det rows eq deep Jac Det 32c0a8f69f5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L143-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepRankOne.lean#L143-L173

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaDensLeibniz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepRankOne
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
open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TubeDeepRankOne

theorem P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_det_rows_eq_deepJacDet_32c0a8f69f5c {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : DifferentiableAt ℂ s y)
    (I : Fin d → Fin n) :
    (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
      (eval y P)⁻¹ * deepJacDet P s I y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TubeDeepRankOne».«det_rows_eq_deepJacDet» := P2M_GroundTheory_Heights__Heights_TubeDeepRankOne_det_rows_eq_deepJacDet_32c0a8f69f5c
