-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_IntegerGeometry_Bits_exact_tape_from_ordered_seeds
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.exact_tape_from_ordered_seeds
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-24T00:31:39.113821+00:00
-- url     : https://prove2.me/theorems/121b81eb-b4d8-4295-aeab-8f203b90c426
-- title:
--   A bounded sequence of point indices restores the exact candidate tape
-- statement:
--   The original ordering of all owned blocks of an anchor and word can be represented by distinct generating points. There are at most n such indices. Once per-entry index sequences are supplied, the executable integer geometry gives exactly the same candidate input predicate for every key encoding, width and memory. This isolates the outer block order from all geometric computations.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_IntegerWindowCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

open StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.IntegerGeometry.Bits.exact_tape_from_ordered_seeds
    (x:World) (m:ℤ→ℤ) (r h:ℕ) :
    let W:=Bits.piece x.n x.mem (r/x.n) (r%x.n)
    ∃ord:ℕ→ℕ→List (Fin x.n),(∀a c,(ord a c).Nodup ∧ (ord a c).length≤x.n) ∧
      let ownedRows:=fun (a c:ℕ)=>Bits.lookup (fun v:Fin x.n=>(ord a c).map (fun p=>Bits.listed (Bits.block m (Bits.win m W v) h c p))) a []
      let t:Instance:={Bits.normalized m W h with owned:=ownedRows}
      ∀(enc:Key→ℕ) (w:ℕ) (mem:ℤ→ℤ),Input x.n mem (tape enc t w) ↔ Input x.n mem (tape enc (data x m r h) w) := by sorry
