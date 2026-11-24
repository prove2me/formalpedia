-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_native_chart_packet_decoder
-- name    : StableMSR.Recovery.NativeWriter.Production.native_chart_packet_decoder
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:11:45.361165+00:00
-- url     : https://prove2.me/theorems/f44b5125-9428-4d84-92cb-2bf287dbafc2
-- title:
--   One native pass decodes symbolic separator events into a physical gate packet
-- statement:
--   For any $n$-point scene and a stored stream of $T$ mask, child, join, and save events, a fixed native RAM command reconstructs the ordered local gates and their signed predecessor displacements at any append position $p$. It writes the root token and gate count at the requested directory slot, including absent or stopped slots. Its running time satisfies $$t\le A(1+n)(1+T)$$ for one absolute constant $A$. The original scene and every previously appended record remain available.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_RegionalProductionTable
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

theorem StableMSR.Recovery.NativeWriter.Production.native_chart_packet_decoder :
  ∃ (A : ℕ) (cmd : Cmd),∀(x : World) (s : Store) (r p : ℕ) (a : Script),
    Ready x s → s.ptrs 3=(r:ℤ) → s.ptrs 4=(p:ℤ) → Stored x.n s.imem a →
    ∃t z, Executes x.dist cmd s t z ∧ z≤A*(1+x.n)*(1+a.events.length) ∧
      Ready x t ∧ (∀i∈[3,4,5],t.ptrs i=s.ptrs i) ∧ t.ptrs 7=(a.packet.gates.size:ℤ) ∧
      (∀j<a.packet.gates.size, Record x.n t (p+j) j (gateAt a.packet.gates j)) ∧
      DirAt t r (a.packet.token,a.packet.gates.size) ∧
      (∀q<p,∀j op,Record x.n s q j op → Record x.n t q j op) ∧
      ∀q<r,∀v,DirAt s q v → DirAt t q v := by sorry
