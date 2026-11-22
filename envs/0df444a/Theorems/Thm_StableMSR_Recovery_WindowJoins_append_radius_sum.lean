-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_append_radius_sum
-- name    : StableMSR.Recovery.WindowJoins.append_radius_sum
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-22T22:37:54.232973+00:00
-- url     : https://prove2.me/theorems/e4b61a52-d440-43ac-bb39-cda55d884f68
-- title:
--   Binary concatenation preserves the exact sum of the two child radii
-- statement:
--   Concatenating two child witnesses of combined count at most k adds their oracle radius sums exactly, including empty children.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix A.6 (tree-decomposition dynamic programming over regional windows), in the mission’s real-distance RAM model.

import Definitions.Def_StableMSR_WindowJoins
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.WindowCSP
open StableMSR.Recovery.WindowProfiles (Mem replace profileSpec Profiles Owned piece keys index active token contains)
open StableMSR.Recovery.RegionalBallDP (Word field word legalize weight Writes)
open StableMSR.Recovery.WindowJoins
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

theorem StableMSR.Recovery.WindowJoins.append_radius_sum (x : World) (a b : ℕ) (h : a+b≤ x.k) (L R : Word) :
    weight x (a+b) (appendWords x.k a (a+b) L R)=weight x a L+weight x b R := by sorry
