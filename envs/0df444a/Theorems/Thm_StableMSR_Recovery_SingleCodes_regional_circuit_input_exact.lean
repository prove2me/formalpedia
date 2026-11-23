-- Prove2me | Theorems.Thm_StableMSR_Recovery_SingleCodes_regional_circuit_input_exact
-- name    : StableMSR.Recovery.SingleCodes.regional_circuit_input_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T00:07:51.320424+00:00
-- url     : https://prove2.me/theorems/0ae01394-c8da-428f-b18e-5a920bbcd3fd
-- title:
--   The concrete circuit input recovers the real window graph, exact menus, edge tests and owned blocks
-- statement:
--   At valid point identifiers the algorithm’s five input functions exactly implement the specified net, directed interaction tests, ball-word menu, boundary compatibility and the point lists for owned blocks.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, https://arxiv.org/abs/2611.03547. This contribution specializes the mission’s tight-block recurrence to singleton progress for the native separator construction.

import Definitions.Def_StableMSR_SingleWindowCodes
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
open StableMSR.Recovery.SingleCodes StableMSR.Recovery.RegionalSeeds StableMSR.Recovery.CartesianBallRows StableMSR.Recovery.FewBallRows

theorem StableMSR.Recovery.SingleCodes.regional_circuit_input_exact (x : World) (W : Cluster x.n) (R : ℝ) (h : ℕ) :
    let d:=instanceOf x W R h;let N:=greedyNet x.dist R W
    (∀v : Point x.n,d.active v.val=true ↔ v∈N) ∧
    (∀u v : ↥N,d.edge u.val.val v.val.val=true ↔ (interactionGraph x.dist R W).Adj u v) ∧
    (∀v : Point x.n,∀P : Partition x.n,P∈traceMenu x h (window x.dist W R v) ↔ ∃c∈d.menu v.val,SingleCodes.decode x (window x.dist W R v) h c=P) ∧
    (∀u v : Point x.n,∀c k,d.test u.val v.val c k=true ↔ compatible (anchor x.dist W R) u v (SingleCodes.decode x (window x.dist W R u) h c) (SingleCodes.decode x (window x.dist W R v) h k)) ∧
    ∀v : Point x.n,∀c : ℕ,∀m : List ℕ,m∈d.owned v.val c ↔
      ∃C∈owned (anchor x.dist W R) v (SingleCodes.decode x (window x.dist W R v) h c),m=C.toList.map Fin.val := by sorry
