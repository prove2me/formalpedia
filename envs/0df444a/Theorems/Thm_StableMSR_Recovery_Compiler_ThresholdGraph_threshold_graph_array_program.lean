-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_ThresholdGraph_threshold_graph_array_program
-- name    : StableMSR.Recovery.Compiler.ThresholdGraph.threshold_graph_array_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-17T14:12:07.278925+00:00
-- url     : https://prove2.me/theorems/388266fe-9645-4656-9494-afe4d8207bfe
-- title:
--   Distance-oracle construction of an exact threshold-graph arc array
-- statement:
--   One fixed deterministic program with $47$ instructions constructs the directed arc array of a distance-threshold graph by querying the distance oracle. For $n$ indexed points, any real threshold $R$, and any integer output base $b$, the program examines every ordered pair, omits self-pairs, and writes exactly the arcs
--   $$E_R=\{(u,v):u\ne v,\ d(u,v)\le R\}.$$
--   No metric or symmetry hypothesis is required for this array construction; when $d$ is symmetric it is a sound complete directed representation of the ordinary simple threshold graph.
--
--   Given only $n$, $b$ and $R$ in designated registers, with otherwise arbitrary initial registers and memory, one actual interpreter run halts after exactly
--   $$T(n)=n(14n+6)+8$$
--   charged steps and makes exactly $n^2$ distance queries. It returns a list of at most $n^2$ arcs encoded as consecutive zero-based endpoint pairs at $b$, the exact arc count in a register, and the endpoint cursor
--   $$b+2|E_R|.$$
--   Every pair occurs in the list if and only if it satisfies the displayed condition. All integer memory outside $[b,b+2n^2)$, all real memory, random-tape position, non-work pointer registers and real registers other than two query scratch registers are preserved. Output cells may initially contain arbitrary data. The threshold register survives. The empty input executes no oracle query and halts in eight steps. Negative thresholds, threshold ties and negative output addresses are included.
--
--   This supplies executable graph-array construction for subsequent connected-component, external-boundary and state-table programs, and can be placed after a generated catalog because it preserves all earlier memory. It is a supporting threshold-graph primitive. Selection of the paper's net/region vertex set, the complete canonical catalog/graph/state-table composition, recurrence evaluation, geometry and full clustering recovery are separate obligations.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, https://arxiv.org/html/2611.03547v1, Section 4.3 and Appendix A.4, construction of local interaction graphs by distance comparisons; supporting instruction-level threshold-graph primitive, not the full net/region construction or a separately numbered paper theorem. Mission 11d3e3d6-df23-4c6a-8fd7-fbb629791a9b.

import Definitions.Def_StableMSR_ComponentGraphMemory
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.ComponentMemory

theorem StableMSR.Recovery.Compiler.ThresholdGraph.threshold_graph_array_program :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 47 ∧
    ∀ (n : ℕ) (d : Point n → Point n → ℝ) (R : ℝ) (b : ℤ) (s : Store),
      s.ptrs 6 = (n:ℤ) → s.ptrs 84 = b → s.regs 89 = R →
      ∀ (ω : ℕ → ℝ) (work : ℕ),
      ∃ es : List (Fin n × Fin n), es.length ≤ n^2 ∧
      let result := (MinSumFPT.step P d ω)^[n*(14*n+6)+8] (s.state 0 work)
      result.halted = true ∧ result.work = work+(n*(14*n+6)+8) ∧
      result.cfg.ptrs 85 = (es.length:ℤ) ∧ result.cfg.ptrs 83 = b+2*(es.length:ℤ) ∧
      EdgeEncoding result.imem b es ∧
      (∀ u v : Fin n, (u,v) ∈ es ↔ u ≠ v ∧ d u v ≤ R) ∧
      (∀ x : ℤ, (x < b ∨ b+2*(n:ℤ)^2 ≤ x) → result.imem x = s.imem x) ∧
      (∀ j : ℕ, j ∉ ([80,81,82,83,85]:List ℕ) → result.cfg.ptrs j = s.ptrs j) ∧
      (∀ j : ℕ, j ≠ 90 → j ≠ 91 → result.cfg.regs j = s.regs j) ∧
      result.cfg.mem = s.mem ∧ result.queries = s.queries+n^2 ∧ result.tapePos = s.tapePos := by sorry
