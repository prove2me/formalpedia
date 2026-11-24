-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Canonical_canonical_resource_bound
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.canonical_resource_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T01:03:18.48991+00:00
-- url     : https://prove2.me/theorems/c6e11b38-d095-4a7d-bda4-9718ca9bd56e
-- title:
--   Resource bounds for the canonically ordered global circuit
-- statement:
--   Let $G$ be the number of gates after canonical local compilation, relocation and padding, $S$ the number of scene rows, and $A=n^{75E(\varepsilon)}$. Then $$G\le 2+SnA.$$ The dense arena uses at most $52\,\mathrm{cap}^4 A$ cells, and its physical formatting pass takes at most $256\,\mathrm{cap}^3 A$ instructions. These bounds include the empty, stopped and padded slots.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_CanonicalRegionalCompiler
set_option linter.all false
set_option maxHeartbeats 2400000
set_option maxRecDepth 20000
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.SingleCircuit StableMSR.Recovery.SingleRAM StableMSR.Recovery.SingleWindows StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.NativeWriter.Production.Candidates StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Canonical.canonical_resource_bound (x : World) (e : ℚ)
    (he : 0 < e) (hl : e < 1) (hn : 2 ≤ x.n) :
    let G := (Canonical.assembly x (budget (e:ℝ)) (widthBound (e:ℝ))).gates.size
    let A := x.n^(75*parameterEnvelope (e:ℝ))
    G ≤ 2+x.rows*x.n*A ∧
    2+5*(1+3*G*x.n*x.n) ≤ 52*x.cap^4*A ∧
    82+42*G+7*(G*x.n) ≤ 256*x.cap^3*A := by sorry
