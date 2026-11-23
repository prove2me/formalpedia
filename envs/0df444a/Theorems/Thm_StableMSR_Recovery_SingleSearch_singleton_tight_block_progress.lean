-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleSearch_singleton_tight_block_progress
-- name    : StableMSR.Recovery.SingleSearch.singleton_tight_block_progress
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T23:59:22.97197+00:00
-- url     : https://prove2.me/theorems/9af9ba33-7a75-441c-a960-8613348797b0
-- title:
--   One new vertex always suffices in a tight width-bounded component
-- statement:
--   A single chosen vertex extends the separator inside a decomposition bag. Each residual component is strictly smaller and has boundary of size at most the original width, contained in this same bag. This removes the second padded bag tuple from candidate enumeration.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleVertexSearch
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 12000
open StableMSR.Recovery StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
open StableMSR.Recovery.DecompositionSearch StableMSR.Recovery.WindowCuts StableMSR.Recovery.SingleSearch
open RobertsonSeymour1986.GM5

theorem StableMSR.Recovery.SingleSearch.singleton_tight_block_progress {V T : Type} [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T]
    {G : SimpleGraph V} {tree : SimpleGraph T} {bags : T→Finset V}
    (htd : IsTreeDecomposition G tree bags) (w : ℕ) (S C : Finset V)
    (hc : IsFlap G S C) (tight : boundary G C=S) (home : ∃t,S⊆bags t) (width : ∀t,(bags t).card≤ w+1) :
    S.card≤ w ∧ ∃v∈C,∃t,insert v S⊆bags t ∧ ∀E∈children G (insert v S) C,
      IsFlap G (boundary G E) E ∧ boundary G E⊆insert v S ∧ (boundary G E).card≤ w ∧ E.card< C.card := by sorry
