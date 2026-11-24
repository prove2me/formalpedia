-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:25.435805+00:00
-- url     : https://prove2.me/theorems/74980753-4a34-4bd8-8cb5-9b06b4ea94f8
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map X c51f5f5b34ef: P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map X c51f5f5b34ef
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map X c51f5f5b34ef construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel segre Map X c51f5f5b34ef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegre.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsSegre.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsMultiDegreePositive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsSegre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} (F : Type) [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef (f : ∀ k, ι k) :
    segreMap F (X ⟨(), f⟩ : MRing (fun _ : Unit => ∀ k, ι k) F) = ∏ k, X ⟨k, f k⟩ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«segreMap_X» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_segreMap_X_c51f5f5b34ef
