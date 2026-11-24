-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362
-- name    : P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:01.140104+00:00
-- url     : https://prove2.me/theorems/c4a8a6f9-5b24-4ebe-a1a4-a00022797483
-- title:
--   P2 M Ground Theory Heights  Heights Regular int Quad cast 144727a14362: P2 M Ground Theory Heights  Heights Regular int Quad cast 144727a14362
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular int Quad cast 144727a14362 construction uses the P2 M Ground Theory Heights  Heights Regular int Quad cast 144727a14362 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PosSemidefOfIntQuadNonneg.lean#L140-L144

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PosSemidefOfIntQuadNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric Matrix Topology Filter
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362 {R : Type*} [CommRing R] {g : ℕ} (B : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    ((intQuad B v : ℤ) : R) = (fun k => (v k : R)) ⬝ᵥ B.map (Int.cast : ℤ → R) *ᵥ fun k => (v k : R) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«intQuad_cast» := P2M_GroundTheory_Heights__Heights_Regular_intQuad_cast_144727a14362
