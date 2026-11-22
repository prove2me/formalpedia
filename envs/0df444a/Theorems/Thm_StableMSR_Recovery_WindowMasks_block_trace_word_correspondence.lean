-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowMasks_block_trace_word_correspondence
-- name    : StableMSR.Recovery.WindowMasks.block_trace_word_correspondence
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:25:44.528659+00:00
-- url     : https://prove2.me/theorems/9e595e16-56ff-4e5e-9126-5d29730a811a
-- title:
--   Derivations of membership-only blocks preserve the full list, exact count, ownership and sum of radii
-- statement:
--   Induction retains the actual list of emitted blocks. A fork concatenates lists, adds their lengths and radius sums, and combines ownership whenever the blocks are pairwise disjoint. Conversely each trace within the count cap has a derivation at its exact length, with that list’s exact payment.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowBlockMasks
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowMasks

theorem StableMSR.Recovery.WindowMasks.block_trace_word_correspondence (x : World) (B : Board) (hk : 1≤ x.k) (hn : 0< x.n)
    (counts : ∀q< B.size,B.arity q=chargeCount x q)
    (values : ∀q< B.size,∀j< x.k,∀s,B.value q j s=oneWord x q j s) :
    (∀p c w,Reach x.k B p c w → ∃L,Trace B (block x) p L ∧ L.length=c ∧
      weight x c w=payment x.dist L ∧ (L.Pairwise Disjoint → Owned x (support L) c w)) ∧
    ∀p L,Trace B (block x) p L → L.length≤ x.k → ∃w,Reach x.k B p L.length w ∧
      weight x L.length w=payment x.dist L := by sorry
