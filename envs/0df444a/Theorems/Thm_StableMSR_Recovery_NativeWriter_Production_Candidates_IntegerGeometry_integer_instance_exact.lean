-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_integer_instance_exact
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.integer_instance_exact
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:17:10.37855+00:00
-- url     : https://prove2.me/theorems/274f6240-e8c4-4d71-bdee-ba27c903a3fd
-- title:
--   An integer distance table preserves the exact ordered regional instance
-- statement:
--   For every positive scale R the finite matrix of integer codes lies in [0,10(n²+1)). At scale n²+1 it gives exactly the original normalized separator instance. Equality holds for the active flags, oriented edges, complete ordered menus, local tests, and ordered owned-block lists, so the entire candidate stream is preserved.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerRegionalGeometry
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.integer_instance_exact (x:World) (W:Cluster x.n) (R:ℝ) (h:ℕ) (m:ℤ→ℤ)
    (hn:0<x.n) (pos:0<R) (metric:IsMetricArray x.dist) (t:Prepared x R m) :
    SingleCodes.instanceOf (matrix x m) W (unit x.n:ℝ) h=SingleCodes.instanceOf x W R h ∧ Bounded x.n m := by sorry
