-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_CutNonempty_proof_ba2e58ffd458
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_CutNonempty_proof_ba2e58ffd458
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:29:55.303136+00:00
-- url     : https://prove2.me/theorems/d523d8ad-a9a5-5927-8333-49566c55994d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Cut Nonempty proof ba2e58ffd458: P2 M Ground Theory Heights  Heights Kleiman Cut Nonempty proof ba2e58ffd458
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Cut Nonempty proof ba2e58ffd458 construction uses the P2 M Ground Theory Heights  Heights Kleiman Cut Nonempty proof ba2e58ffd458 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PCutNonempty.lean#L78-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CutOneGeneratorSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCutNonempty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Irrelevant_proof_a0f9d6421b8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_PrimeFiltration_Point_proof_d22f31b4a055

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_CutNonempty_proof_ba2e58ffd458 (hO : CutOneGenerator.Statement.{u, w}) : CutNonempty.Statement.{u, w} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«CutNonempty».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_CutNonempty_proof_ba2e58ffd458
