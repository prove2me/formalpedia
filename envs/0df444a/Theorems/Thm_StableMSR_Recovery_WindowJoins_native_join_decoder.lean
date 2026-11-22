-- Prove2me | Theorems.Thm_StableMSR_Recovery_WindowJoins_native_join_decoder
-- name    : StableMSR.Recovery.WindowJoins.native_join_decoder
-- status  : Open
-- author  : @lreyzin
-- created : 2026-11-22T22:37:54.608801+00:00
-- url     : https://prove2.me/theorems/dff4ad22-83e0-44e3-bd3c-17b8dd3a8894
-- title:
--   A fixed polynomial distance-RAM program selects regional optima from explicit binary join records
-- statement:
--   One fixed real-distance RAM command evaluates all the binary join states, reconstructs endpoint words, and restores the original scenario dimension. Its polynomial in the expanded table size is independent of stability.
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

theorem StableMSR.Recovery.WindowJoins.native_join_decoder : ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (e : ℚ) (H : ℕ) (s : Store),
    0< x.k → 0< x.n → let y:=worldOf x.k H x.dist s
    Ready y s → Encodes x e y → ∃t z,Executes x.dist cmd s t z ∧ z≤ p.eval y.cap ∧
    Ready (worldOf x.k x.rows x.dist t) t ∧ Profiles x e (worldOf x.k x.rows x.dist t).mem := by sorry
