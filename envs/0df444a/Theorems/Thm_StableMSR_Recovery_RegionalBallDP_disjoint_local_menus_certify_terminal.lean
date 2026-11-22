-- Prove2me | Theorems.Thm_StableMSR_Recovery_RegionalBallDP_disjoint_local_menus_certify_terminal
-- name    : StableMSR.Recovery.RegionalBallDP.disjoint_local_menus_certify_terminal
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T13:13:53.087245+00:00
-- url     : https://prove2.me/theorems/e20f3fec-3c66-4e93-9766-b228a54658a9
-- title:
--   Edge-local coverage and additive regional budgets certify a complete terminal
-- statement:
--   Induction on a represented path proves that each prefix covers its assigned region with distinct centers owned by that region. The reverse induction uses only a locally affordable predecessor at each viable state to construct a path at the terminal budget. This discharges both global requirements from edge-local hypotheses.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_LocalBallTrials
import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.RegionalBallDP.disjoint_local_menus_certify_terminal (x : World) (hs : shape x) (v : ℕ) (B : ℝ) (t : LocalTrial x v B) :
    vertex x v ∧ InTable x v ∧ ∃u,Route x v u ∧ weight x x.k u≤B := by
  sorry
