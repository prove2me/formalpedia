-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_irreducible_of_fixed
-- name    : PositivityTheory.RgUd.Prod.Asm.irreducible_of_fixed
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:02:57.535061+00:00
-- url     : https://prove2.me/theorems/6fe9c751-886d-4ca0-aac7-be1e8b2bcc9f
-- title:
--   Asm: irreducible of fixed
-- statement:
--   The Asm construction uses the irreducible of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L57-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L57-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CentralProducts_UnitarisableHypotheses_IrrSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.Prod PositivityTheory.RgUd.Prod.Asm
open GlobalTheory.PRep
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

theorem PositivityTheory.RgUd.Prod.Asm.irreducible_of_fixed (K : Subgroup G)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (W : Subrepresentation ρ) (h1 : fixed ρ K ⊓ W.toSubmodule ≠ ⊥)
    (h2 : ∀ U : Subrepresentation ρ, U.toSubmodule ≤ W.toSubmodule → fixed ρ K ⊓ U.toSubmodule ≠ ⊥ →
      fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule)
    (h3 : ∀ U : Subrepresentation ρ, fixed ρ K ⊓ W.toSubmodule ≤ U.toSubmodule →
      W.toSubmodule ≤ U.toSubmodule) :
    W.toRepresentation.IsIrreducible := by sorry
