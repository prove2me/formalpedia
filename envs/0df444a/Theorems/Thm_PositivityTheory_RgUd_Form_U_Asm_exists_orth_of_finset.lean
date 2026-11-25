-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_exists_orth_of_finset
-- name    : PositivityTheory.RgUd.Form.U.Asm.exists_orth_of_finset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:00.425698+00:00
-- url     : https://prove2.me/theorems/cf2aa272-a35c-4cdc-a777-27b7bdc13838
-- title:
--   Asm: exists orth of finset
-- statement:
--   The Asm construction uses the exists orth of finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L15-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L15-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_HermitianForms_UnitaryLattices_UnitaryHypotheses_ExistsOrthOfFinset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U PositivityTheory.RgUd.Form.U.Asm

theorem PositivityTheory.RgUd.Form.U.Asm.exists_orth_of_finset {D : Type} [AddCommGroup D] [Module ℂ D] (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re) (s : Finset D) :
    ∀ u : D, ∃ w ∈ Submodule.span ℂ (s : Set D), ∀ m ∈ Submodule.span ℂ (s : Set D), B (u - w) m = 0 := by sorry
