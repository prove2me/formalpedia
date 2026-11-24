-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_mem_fixed_iff
-- name    : PositivityTheory.RgUd.Prod.Asm.mem_fixed_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:51.029199+00:00
-- url     : https://prove2.me/theorems/ebd2a3e2-b8d1-4fea-8f1a-59dfbbfb937b
-- title:
--   Asm: mem fixed iff
-- statement:
--   The Asm construction uses the mem fixed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L16-L18

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

theorem PositivityTheory.RgUd.Prod.Asm.mem_fixed_iff (K : Subgroup G) (v : V) : v ∈ fixed ρ K ↔ ∀ k : K, ρ (k : G) v = v := by sorry
