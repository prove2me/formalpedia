-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_computed_integer_instance
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.computed_integer_instance
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:56:51.141713+00:00
-- url     : https://prove2.me/theorems/23462710-13d9-4c9a-895c-59f544ed08c1
-- title:
--   The computable integer compiler input equals the canonically ordered metric input
-- statement:
--   Fix a positive-scale slot in a metric scene and its prepared integer distance table. The active vertices, adjacency, menus, compatibility tests and every ordered list of owned blocks computed from that table agree exactly with the canonical metric instance. This supplies a deterministic source for the regional compiler.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.computed_integer_instance (x:World) (r h:ℕ) (m:ℤ→ℤ)
  (hn:0<x.n) (pos:0<scale x (r/x.n)) (metric:IsMetricArray x.dist) (prep:Prepared x (scale x (r/x.n)) m) :
  Canonical.integerData x.n x.mem m r h = Canonical.arrange (SingleCodes.instanceOf x (WindowProfiles.piece x (r/x.n) (r%x.n)) (scale x (r/x.n)) h) := by sorry
