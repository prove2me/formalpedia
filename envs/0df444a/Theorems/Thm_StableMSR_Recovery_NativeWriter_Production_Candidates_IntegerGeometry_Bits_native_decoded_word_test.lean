-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Bits_native_decoded_word_test
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.native_decoded_word_test
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:39:51.965082+00:00
-- url     : https://prove2.me/theorems/392e9b9b-9662-4457-adca-26974e3ee2d3
-- title:
--   The native compatibility scan returns the exact test bit for two decoded window words
-- statement:
--   Initialize the row-membership arrays using the integer ball-word decoder and the owner columns using the greedy regional net. The fixed cubic-time integer program then computes the original compiler’s exact test bit for the two anchors and words. Filling unused source rows with empty sets gives an n by n rectilinear layout and leaves the accepted-row families unchanged.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerWindowCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry
open scoped Classical

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.native_decoded_word_test :
  ∃cmd:Cmd,IntegerCmd cmd ∧ ∀
(x:World) (s:Store) (m:ℤ→ℤ) (r h:ℕ) (a b:Fin x.n) (c k:ℕ),
    let W:=Bits.piece x.n x.mem (r/x.n) (r%x.n)
    let A:=Bits.owner m (Bits.net m W)
    let L:=fun i:Fin x.n=>if i∈Bits.win m W a then Bits.block m (Bits.win m W a) h c i else ∅
    let R:=fun i:Fin x.n=>if i∈Bits.win m W b then Bits.block m (Bits.win m W b) h k i else ∅
    s.ptrs 0=(x.n:ℤ) →
    (∀i p:Fin x.n,s.imem (s.ptrs 30+(i.val:ℤ)*(x.n:ℤ)+(p.val:ℤ))=(if p∈L i then 1 else 0) ∧
      s.imem (s.ptrs 31+(i.val:ℤ)*(x.n:ℤ)+(p.val:ℤ))=(if p∈R i then 1 else 0)) →
    (∀p:Fin x.n,s.imem (s.ptrs 32+(p.val:ℤ))=(if A p=a then 1 else 0) ∧
      s.imem (s.ptrs 33+(p.val:ℤ))=(if A p=b then 1 else 0)) →
    ∃t z,Executes x.dist cmd s t z ∧ z≤100*(1+x.n)^3 ∧ t.imem=s.imem ∧ t.mem=s.mem ∧ t.queries=s.queries ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 37=(if (data x m r h).test a.val b.val c k then 1 else 0) := by sorry
