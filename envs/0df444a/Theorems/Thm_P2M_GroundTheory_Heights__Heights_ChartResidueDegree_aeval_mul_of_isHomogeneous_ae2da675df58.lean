-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58
-- name    : P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:58.22092+00:00
-- url     : https://prove2.me/theorems/b5cc8acb-5836-4b4e-a296-bac793784fc9
-- title:
--   P2 M Ground Theory Heights  Heights Chart Residue Degree aeval mul of is Homogeneous ae2da675df58: P2 M Ground Theory Heights  Heights Chart Residue Degree aeval mul of is Homogeneous ae2da675df58
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Residue Degree aeval mul of is Homogeneous ae2da675df58 construction uses the P2 M Ground Theory Heights  Heights Chart Residue Degree aeval mul of is Homogeneous ae2da675df58 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L15-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartResidueDegree.lean#L15-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
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
open GroundTheory.Heights₂.Heights.ChartResidueDegree

theorem P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58 {F : Type} [Field F] {n : ℕ} {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (a : A) (x : Fin n → A) :
    aeval (fun m => a * x m) g = a ^ d * aeval x g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartResidueDegree».«aeval_mul_of_isHomogeneous» := P2M_GroundTheory_Heights__Heights_ChartResidueDegree_aeval_mul_of_isHomogeneous_ae2da675df58
