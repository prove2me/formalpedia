-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_firstCoords_mem_zeroSet_92c58088a2c7
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelFibre_firstCoords_mem_zeroSet_92c58088a2c7
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:26.462563+00:00
-- url     : https://prove2.me/theorems/c7b8c244-6d77-47bd-ad5f-f275642649bb
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Fibre first Coords mem zero Set 92c58088a2c7: P2 M Ground Theory Heights  Heights Normal Model Fibre first Coords mem zero Set 92c58088a2c7
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Fibre first Coords mem zero Set 92c58088a2c7 construction uses the P2 M Ground Theory Heights  Heights Normal Model Fibre first Coords mem zero Set 92c58088a2c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L17-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalModelProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PModelLocalizationMaximalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_NormalModelFibreNear
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
open MvPolynomial Filter Topology ComplexSets Metric
noncomputable section
open GroundTheory.Heights₂.Heights.NormalModelFibre
variable {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)

theorem P2M_GroundTheory_Heights__Heights_NormalModelFibre_firstCoords_mem_zeroSet_92c58088a2c7 {w : Fin n ⊕ Fin M.m → ℂ} (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) :
    IndefiniteRowSideFullHecke.ComplexSets.firstCoords w ∈ zeroSet J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelFibre».«firstCoords_mem_zeroSet» := P2M_GroundTheory_Heights__Heights_NormalModelFibre_firstCoords_mem_zeroSet_92c58088a2c7
