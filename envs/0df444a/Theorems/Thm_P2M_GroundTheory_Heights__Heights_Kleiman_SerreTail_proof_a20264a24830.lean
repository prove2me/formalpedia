-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SerreTail_proof_a20264a24830
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SerreTail_proof_a20264a24830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:13.841805+00:00
-- url     : https://prove2.me/theorems/14c33fd2-2b86-4af9-afc2-032867426d39
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Serre Tail proof a20264a24830: P2 M Ground Theory Heights  Heights Kleiman Serre Tail proof a20264a24830
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Serre Tail proof a20264a24830 construction uses the P2 M Ground Theory Heights  Heights Kleiman Serre Tail proof a20264a24830 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreTail.lean#L13-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreTail.lean#L13-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreTail
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
universe u v

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SerreTail_proof_a20264a24830 (hFin : SerreFinite.Statement.{u, v}) (hOnto : SerreOnto.Statement.{u, v}) :
    SerreTail.Statement.{u, v} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SerreTail».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SerreTail_proof_a20264a24830
