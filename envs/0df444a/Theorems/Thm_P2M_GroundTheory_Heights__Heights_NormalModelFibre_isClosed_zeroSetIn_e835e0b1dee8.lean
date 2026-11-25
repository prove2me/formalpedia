-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8
-- name    : P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:22.43994+00:00
-- url     : https://prove2.me/theorems/80bf8833-8481-452f-86a9-994c91330927
-- title:
--   P2 M Ground Theory Heights  Heights Normal Model Fibre is Closed zero Set In e835e0b1dee8: P2 M Ground Theory Heights  Heights Normal Model Fibre is Closed zero Set In e835e0b1dee8
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Model Fibre is Closed zero Set In e835e0b1dee8 construction uses the P2 M Ground Theory Heights  Heights Normal Model Fibre is Closed zero Set In e835e0b1dee8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/NormalModelFibreNear.lean#L61-L66

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

theorem P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8 : IsClosed (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalModelFibre».«isClosed_zeroSetIn» := P2M_GroundTheory_Heights__Heights_NormalModelFibre_isClosed_zeroSetIn_e835e0b1dee8
