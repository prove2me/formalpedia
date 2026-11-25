-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Form_U_Asm_mem_fixed_iff_irr
-- name    : PositivityTheory.RgUd.Form.U.Asm.mem_fixed_iff_irr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:50:01.06141+00:00
-- url     : https://prove2.me/theorems/728982f9-fda9-4dc4-911c-4ea37118aba2
-- title:
--   Asm: mem fixed iff irr
-- statement:
--   The Asm construction uses the mem fixed iff irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L10-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/HermitianForms/UnitaryLattices/UnitaryHypotheses/ExistsOrthOfFinset.lean#L10-L13

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

theorem PositivityTheory.RgUd.Form.U.Asm.mem_fixed_iff_irr {G D : Type} [Group G] [AddCommGroup D] [Module ℂ D] (ρ : Representation ℂ G D)
    (K : Subgroup G) (v : D) : v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by sorry
