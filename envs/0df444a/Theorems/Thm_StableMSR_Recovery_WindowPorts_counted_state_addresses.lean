-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowPorts_counted_state_addresses
-- name    : StableMSR.Recovery.WindowPorts.counted_state_addresses
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T23:18:48.036996+00:00
-- url     : https://prove2.me/theorems/d7957e26-33bd-4e0a-85f2-fea6a1c28dfe
-- title:
--   Counted left and completed labels have distinct topologically ordered addresses
-- statement:
--   The flat count states retain their exact widths, fit inside one plus the number of port slots times n squared, and respect every predecessor order. Intermediate and completed labels are disjoint.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution gives explicit counted join records for the mission's real-distance RAM.

import Definitions.Def_StableMSR_WindowPorts
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP StableMSR.Recovery.WindowJoins
open StableMSR.Recovery.WindowProfiles (piece index keys Owned divN remN)
open StableMSR.Recovery.RegionalBallDP (Word field weight legalize Writes)
open StableMSR.Recovery.WindowPorts

theorem StableMSR.Recovery.WindowPorts.counted_state_addresses (B : Board) (n k : ℕ) (hk : 1≤ k) (kn : k< n) :
    (∀p< B.size,∀i≤ k,stage n p i< volume B.size n ∧ finish n p i< volume B.size n ∧
      (lower B n k).len (stage n p i)=i ∧ (lower B n k).len (finish n p i)=i) ∧
    (∀p q i j,i≤ k → j≤ k → p< q → finish n p i< stage n q j) ∧
    (∀p i j,i≤ k → j≤ k → stage n p i< finish n p j) ∧
    (∀p q i j,i≤ k → j≤ k → stage n p i≠finish n q j) ∧
    (∀p q i j,i≤ k → j≤ k → finish n p i=finish n q j → p=q ∧ i=j) ∧
    (∀p q i j,i≤ k → j≤ k → stage n p i=stage n q j → p=q ∧ i=j) := by sorry
