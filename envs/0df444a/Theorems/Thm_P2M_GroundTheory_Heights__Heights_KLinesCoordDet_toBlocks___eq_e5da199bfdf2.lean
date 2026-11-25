-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2
-- name    : P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:31.90143+00:00
-- url     : https://prove2.me/theorems/6f5d1e4e-2a22-596c-b644-6eafbbce0a98
-- title:
--   P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq e5da199bfdf2: P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq e5da199bfdf2
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq e5da199bfdf2 construction uses the P2 M Ground Theory Heights  Heights KLines Coord Det to Blocks   eq e5da199bfdf2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesCoordDet.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesCoordDet
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
open Matrix
open GroundTheory.Heights₂.Heights.KLinesCoordDet
variable {K : Type} [Field K] {n m k : ℕ} (B : Module.Basis (Fin m ⊕ Fin k) K (Fin n → K))
  (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)

theorem P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2 (hb : ∀ i, B (Sum.inl i) = b i) :
    (B.toMatrix (Sum.elim b c)).toBlocks₁₁ = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesCoordDet».«toBlocks₁₁_eq» := P2M_GroundTheory_Heights__Heights_KLinesCoordDet_toBlocks___eq_e5da199bfdf2
