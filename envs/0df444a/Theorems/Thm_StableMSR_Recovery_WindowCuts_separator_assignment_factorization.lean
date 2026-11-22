-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowCuts_separator_assignment_factorization
-- name    : StableMSR.Recovery.WindowCuts.separator_assignment_factorization
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:40:37.895715+00:00
-- url     : https://prove2.me/theorems/7595c2be-39a7-4f1a-a275-f940acbe7019
-- title:
--   Independent component assignments glue exactly across a progress bag
-- statement:
--   A bag label and one prescribed interior labeling per connected piece extend jointly exactly when the bag and each piece with its true boundary satisfy their local domain and edge tests. Both orientations of an edge are covered for arbitrary asymmetric label tests. No selection of an optimal child solution is involved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowSeparatorCuts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned subR divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts
open StableMSR.Recovery.WindowCuts

theorem StableMSR.Recovery.WindowCuts.separator_assignment_factorization {V X : Type} [DecidableEq V] (G : SimpleGraph V) (D : V→Finset X) (test : V→V→X→X→Prop)
    (T : Finset V) (K : Finset (Finset V))
    (away : ∀C∈K,Disjoint C T)
    (split : ∀C∈K,∀E∈K,C≠E → Disjoint C E ∧ ∀v∈C,∀w∈E,¬G.Adj v w)
    (a : V→X) (f : Finset V→V→X) :
    (∃g : V→X,okay G D test (total T K) g ∧ (∀v∈T,g v=a v) ∧ ∀C∈K,∀v∈C,g v=f C v) ↔
      okay G D test T a ∧ ∀C∈K,okay G D test (C∪rim G (total T K) C) (patch C a (f C)) := by sorry
