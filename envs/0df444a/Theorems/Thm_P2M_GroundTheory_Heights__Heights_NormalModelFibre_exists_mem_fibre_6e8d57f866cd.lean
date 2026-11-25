-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_exists_mem_fibre_6e8d57f866cd
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelFibre_exists_mem_fibre_6e8d57f866cd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:15.6968+00:00
-- url     : https://prove2.me/theorems/9d7fdd7e-0a47-491e-ae40-a21d421eee35
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Fibre exists mem fibre 6e8d57f866cd: P2 M Ground Theory Heights  Heights Normal Model Fibre exists mem fibre 6e8d57f866cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Fibre exists mem fibre 6e8d57f866cd construction uses the P2 M Ground Theory Heights  Heights Normal Model Fibre exists mem fibre 6e8d57f866cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L28-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L28-L47

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

theorem P2M_GroundTheory_Heights__Heights_NormalModelFibre_exists_mem_fibre_6e8d57f866cd {q : Fin n → ℂ} (hq : q ∈ zeroSet J) :
    ∃ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelFibre».«exists_mem_fibre» := P2M_GroundTheory_Heights__Heights_NormalModelFibre_exists_mem_fibre_6e8d57f866cd
