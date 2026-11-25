-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:07.904949+00:00
-- url     : https://prove2.me/theorems/7fe6e74f-8d29-4483-87df-88051bb901a5
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Extension Proof of Gens piece le b01126a46004: P2 M Ground Theory Heights  Heights Kleiman Extension Proof of Gens piece le b01126a46004
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Extension Proof of Gens piece le b01126a46004 construction uses the P2 M Ground Theory Heights  Heights Kleiman Extension Proof of Gens piece le b01126a46004 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L191-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PExtension.lean#L191-L199

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.ExtensionProof
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]

theorem P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004 {ι : Type} [Fintype ι] (deg : ι → ℤ) (gen : ι → E) {V : ℤ → Submodule S E}
    (hV : ∀ k, gen k ∈ V (deg k))
    (hsmul : ∀ (f : Poly S N) (d : ℕ) (c : ℤ) (m : E), f.IsHomogeneous d → m ∈ V c →
      aeval x f • m ∈ V (c + d)) (c : ℤ) : (ofGens (S := S) (x := x) deg gen).piece c ≤ V c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«ExtensionProof».«ofGens_piece_le» := P2M_GroundTheory_Heights__Heights_Kleiman_ExtensionProof_ofGens_piece_le_b01126a46004
