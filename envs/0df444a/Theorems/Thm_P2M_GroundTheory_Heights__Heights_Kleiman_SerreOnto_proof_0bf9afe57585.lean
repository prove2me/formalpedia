-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SerreOnto_proof_0bf9afe57585
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SerreOnto_proof_0bf9afe57585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:31:20.579459+00:00
-- url     : https://prove2.me/theorems/79b8b262-6e5f-48a1-ac2d-be2122103577
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Serre Onto proof 0bf9afe57585: P2 M Ground Theory Heights  Heights Kleiman Serre Onto proof 0bf9afe57585
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Serre Onto proof 0bf9afe57585 construction uses the P2 M Ground Theory Heights  Heights Kleiman Serre Onto proof 0bf9afe57585 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L330-L375
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L330-L375

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
universe u v w w'

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SerreOnto_proof_0bf9afe57585 (hC : CechExact.Statement.{u, max u v})
    (hF : SerreFree.Statement.{u, max u v}) (hV : SerreVanish.Statement.{u, max u v}) :
    SerreOnto.Statement.{u, v} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SerreOnto».«proof» := P2M_GroundTheory_Heights__Heights_Kleiman_SerreOnto_proof_0bf9afe57585
