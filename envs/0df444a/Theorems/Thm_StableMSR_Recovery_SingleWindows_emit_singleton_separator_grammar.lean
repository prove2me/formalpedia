-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleWindows_emit_singleton_separator_grammar
-- name    : StableMSR.Recovery.SingleWindows.emit_singleton_separator_grammar
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:03:26.095902+00:00
-- url     : https://prove2.me/theorems/6deb6492-8944-41d4-b2ff-ecede0ed1584
-- title:
--   Emit the one-vertex window grammar into native RAM
-- statement:
--   Emit the explicitly defined one-vertex grammar on the canonical window graph. A transition chooses one vertex and one label; its children are the components left after deleting that vertex and the current boundary. Give private ordered joins to alternatives and preserve the generated owned-block sets within the uniform real-distance RAM bound.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleWindowGrammar
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5
open StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.Supplement
open StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowPorts StableMSR.Recovery.WindowMasks StableMSR.Recovery.SingleWindows
open StableMSR.Recovery.WindowProfiles (piece keys)

theorem StableMSR.Recovery.SingleWindows.emit_singleton_separator_grammar : ∃c D b : ℕ,0< c ∧ 0< b ∧ ∀e : ℚ,0< e → e<1 → ∃cmd : Cmd,nativeSpec e c D b cmd := by sorry
