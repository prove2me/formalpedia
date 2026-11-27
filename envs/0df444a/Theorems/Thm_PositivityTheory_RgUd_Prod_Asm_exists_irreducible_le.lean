-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_exists_irreducible_le
-- name    : PositivityTheory.RgUd.Prod.Asm.exists_irreducible_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:54:38.407324+00:00
-- url     : https://prove2.me/theorems/c49e2a09-c4bc-4363-8bf5-2eccf65b3f15
-- title:
--   Asm: exists irreducible le
-- statement:
--   The Asm construction uses the exists irreducible le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L127-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L127-L174

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

theorem PositivityTheory.RgUd.Prod.Asm.exists_irreducible_le {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (hsmall : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (hA : GlobalTheory.PRep.IsAdmissible ρ)
    (hcompl : ∀ S : Subrepresentation ρ, ∃ T : Subrepresentation ρ, IsCompl S.toSubmodule T.toSubmodule)
    (S : Subrepresentation ρ) (hS : S ≠ ⊥) :
    ∃ S₀ : Subrepresentation ρ, S₀ ≠ ⊥ ∧ S₀.toSubmodule ≤ S.toSubmodule ∧ S₀.toRepresentation.IsIrreducible := by sorry
