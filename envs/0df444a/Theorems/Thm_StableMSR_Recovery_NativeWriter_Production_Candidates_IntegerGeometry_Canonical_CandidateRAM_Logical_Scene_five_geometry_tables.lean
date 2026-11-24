-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_CandidateRAM_Logical_Scene_five_geometry_tables
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.five_geometry_tables
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T20:56:46.900865+00:00
-- url     : https://prove2.me/theorems/70d5afa0-b89b-43ff-b5ca-5d9e7c90594e
-- title:
--   The integer regional program constructs the five geometry tables
-- statement:
--   Let $W$ be a regional piece of an $n$-point instance and let $N$ be the greedy net computed in its ranked integer memory. Starting with the prepared heap, the first 24 geometry commands write the indicators of $N$ and $W$, the least eligible owner of each point (with self as fallback), and both square matrices. The window entry at $(a,p)$ records membership of $p$ in the directed $4U$ window of $a$. The edge entry at $(p,a)$ requires distinct points and both directed entries at most $8U$, where $U$ is the integer scale. Control registers, output, and the remaining heap obey the regional geometry interface. If $C$ is the input capacity, the charge is at most $$350C+2000(n+1)^3.$$
-- source:
--   Implementation of the root-component and boundary requests in Appendix A.6 of Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/abs/2611.03547.

import Definitions.Def_StableMSR_RegionalGeometryTables
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM
open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.CandidateRAM.Logical.Scene.five_geometry_tables (x:World) (m:Store) (r h w:ℕ) (s:Logical.State)
    (hn:0<x.n) (hr:r<x.rows*x.n) (ready:Ready x m) (prepared:Logical.Prepared x.n r h w s) :
    ∃t k,Logical.Executes x.n m.imem Scene.geometryPrefix s t k ∧
      k ≤ 350*x.cap + 2000*(x.n+1)^3 ∧
      Scene.GeometryImage m.imem (WindowProfiles.piece x (r/x.n) (r%x.n)) h s t := by sorry
