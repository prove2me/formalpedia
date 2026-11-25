-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_exists_orth_decomp
-- name    : PositivityTheory.RgUd.Form.U.Asm.exists_orth_decomp
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:49.542825+00:00
-- url     : https://prove2.me/theorems/985b1b14-a48a-5d24-be8f-f4b8af02d087
-- title:
--   Asm: exists orth decomp
-- statement:
--   The Asm construction uses the exists orth decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L66-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L66-L166

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

theorem PositivityTheory.RgUd.Form.U.Asm.exists_orth_decomp {G D : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup D]
    [Module ℂ D] (ρ : Representation ℂ G D) (hA : IsAdmissible ρ) (K₁ : Subgroup G) (hK₁o : IsOpen (K₁ : Set G))
    (hK₁c : IsCompact (K₁ : Set G)) (χ : G → ℝ) (B : D →ₗ[ℂ] D →ₗ⋆[ℂ] ℂ)
    (hBp : ∀ x, x ≠ 0 → 0 < (B x x).re)
    (hBe : ∀ g x y, B (ρ g x) (ρ g y) = (χ g : ℂ) * B x y) (W : Submodule ℂ D)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (u : D) :
    ∃ w ∈ W, ∀ w' ∈ W, B (u - w) w' = 0 := by sorry
