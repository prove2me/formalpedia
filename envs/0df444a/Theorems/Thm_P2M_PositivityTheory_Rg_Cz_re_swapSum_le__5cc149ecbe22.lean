-- Prove2me | Theorems.Thm_P2M_PositivityTheory_Rg_Cz_re_swapSum_le__5cc149ecbe22
-- name    : P2M_PositivityTheory_Rg_Cz_re_swapSum_le__5cc149ecbe22
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:09:58.498055+00:00
-- url     : https://prove2.me/theorems/22ad6f7e-c17a-45ba-8c97-563b32485369
-- title:
--   P2 M Positivity Theory Rg Cz re swap Sum le  5cc149ecbe22: P2 M Positivity Theory Rg Cz re swap Sum le  5cc149ecbe22
-- statement:
--   The P2 M Positivity Theory Rg Cz re swap Sum le  5cc149ecbe22 construction uses the P2 M Positivity Theory Rg Cz re swap Sum le  5cc149ecbe22 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L29-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/CasimirAlgebra/KugaCoordinates/CasimirBounds/ReSwapSumLe.lean#L29-L83

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_KTypeData
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_CasimirBounds_ReSwapSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
set_option linter.unusedSectionVars false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {n : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]

theorem P2M_PositivityTheory_Rg_Cz_re_swapSum_le__5cc149ecbe22 (f : TV n ℂ Q) (B : Finset Q) (p : Q)
    (hp : p ∉ B) (hf : ∀ q ∈ B, ∀ q' ∈ B, q ≠ q' → pm (Equiv.swap q q') f = -f) :
    (∑ q ∈ B, star f ⬝ᵥ pm (Equiv.swap p q) f).re ≤ (star f ⬝ᵥ f).re := by sorry

alias «PositivityTheory».«Rg».«Cz».«re_swapSum_le'» := P2M_PositivityTheory_Rg_Cz_re_swapSum_le__5cc149ecbe22
