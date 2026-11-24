-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_compiler_preserves_unordered_language
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.compiler_preserves_unordered_language
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:57:06.160867+00:00
-- url     : https://prove2.me/theorems/4ab3410e-6bfa-4fe0-8d51-addf9d0c03bc
-- title:
--   Canonical block order preserves the regional language up to permutation
-- statement:
--   For any finite separator instance, sort the points within each owned block and order those blocks lexicographically. The resulting circuit has a valid root, and each word recognized by either circuit has a permutation recognized by the other. Multiplicities of blocks are preserved. This permits a deterministic choice of literal order in the clustering algorithm.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.compiler_preserves_unordered_language (n:ℕ) (d:Instance) (w:ℕ) :
  let g:=compileRegion (Canonical.arrange d) w
  let t:=compileRegion d w
  g.2<g.1.size ∧ Canonical.Equivalent n g.1 g.2 t.1 t.2 := by sorry
