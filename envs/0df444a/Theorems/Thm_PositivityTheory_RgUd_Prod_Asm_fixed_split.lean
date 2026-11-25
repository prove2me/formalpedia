-- Prove2me | Theorems.Thm_PositivityTheory_RgUd_Prod_Asm_fixed_split
-- name    : PositivityTheory.RgUd.Prod.Asm.fixed_split
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:54.091188+00:00
-- url     : https://prove2.me/theorems/9a6e1ef0-df65-400c-b9d6-6e155d32dd57
-- title:
--   Asm: fixed split
-- statement:
--   The Asm construction uses the fixed split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/UnitaryDualProof/CentralProducts/UnitarisableHypotheses/IrrSub.lean#L44-L55

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

theorem PositivityTheory.RgUd.Prod.Asm.fixed_split (U C : Subrepresentation ρ) (hUC : U.toSubmodule ⊓ C.toSubmodule = ⊥) (g : G)
    {u c : V} (hu : u ∈ U.toSubmodule) (hc : c ∈ C.toSubmodule) (h : ρ g (u + c) = u + c) :
    ρ g u = u := by sorry
