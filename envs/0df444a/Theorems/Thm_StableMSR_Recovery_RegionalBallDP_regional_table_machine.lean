-- Prove2me | Theorems.Thm_StableMSR_Recovery_RegionalBallDP_regional_table_machine
-- name    : StableMSR.Recovery.RegionalBallDP.regional_table_machine
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-21T13:12:44.842033+00:00
-- url     : https://prove2.me/theorems/e049b03d-df49-49f8-9ed9-355be84a18ba
-- title:
--   Polynomial distance-RAM execution of all regional relaxation rounds
-- statement:
--   A single deterministic distance-oracle RAM program initializes the table, executes exactly H simultaneous Bellman updates for H table rows, and normalizes the output. A full mathematical history witnesses those updates. The polynomial is uniform in the dimensions, metric and table contents.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, equation (2), and Appendix A.4–A.6. Real-distance oracle implementation and witness reconstruction for the Prove2Me recovery mission.

import Definitions.Def_StableMSR_RegionalBallDP
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows
open StableMSR.Recovery.RegionalBallDP
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem StableMSR.Recovery.RegionalBallDP.regional_table_machine :
    ∃p : Polynomial ℕ,∃cmd : Cmd,∀(x : World) (s : Store),0<x.k → 0<x.rows → Ready x s →
    ∃t z,Executes x.dist cmd s t z ∧ z≤p.eval x.cap ∧
      let y:=worldOf x.k x.rows x.dist t
      Ready y t ∧ ∃h : ℕ→ℕ→ℤ,
        Writes x (withMem x (h 0)) seedTable ∧
        (∀i<x.rows,Writes (withMem x (h i)) (withMem x (h (i+1))) tick) ∧
        Writes (withMem x (h x.rows)) y clean := by
  sorry
