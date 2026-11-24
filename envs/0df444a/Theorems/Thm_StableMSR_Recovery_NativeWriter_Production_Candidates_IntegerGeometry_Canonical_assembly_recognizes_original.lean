-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_assembly_recognizes_original
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly_recognizes_original
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:57:41.863024+00:00
-- url     : https://prove2.me/theorems/fae18fb4-837b-466c-8e3c-560189343388
-- title:
--   The canonically ordered global circuit recognizes exactly the required regional partitions
-- statement:
--   For every scene table on a nonempty point set, the circuit assembled from lexicographically ordered local block lists realizes the original regional grammar at every slot. In particular, its live roots produce precisely the generated partitions and each accepted word has distinct blocks. Missing representatives and nonpositive scales have their stipulated root languages.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.assembly_recognizes_original (x:World) (e:ℚ) (hn:0<x.n) :
  let a:=Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))
  RegionalLanguage x e a.gates a.roots := by sorry
