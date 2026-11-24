-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_regional_key_operand_bound
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.regional_key_operand_bound
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:46:33.842481+00:00
-- url     : https://prove2.me/theorems/925fa46e-5408-46e5-9645-ae02b9aa62a1
-- title:
--   Every requested or installed regional key has a short native integer representation
-- statement:
--   On an n-point window instance define K=(h+1)n^{2(h+1)}. Every key requested by a child, installed at a boundary row, or requested by a root component has a serialized representation with at most 3n+1 integers and sum at most n(2n+K). This bound includes failed candidates, empty rows, and the default label of a restriction. It is uniform in the naming function and the separator width. Together with the native injective key encoder it bounds the work of constructing any operand.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.regional_key_operand_bound
    (x:World) (W:Cluster x.n) (R:ℝ) (h w:ℕ) (enc:Key→ℕ) (hn:1≤x.n) (op:Candidates.Instr)
    (mem:op∈tape enc (SingleCodes.instanceOf x W R h) w) (id:ℕ)
    (use:op=.need id ∨ op=.seal id) :
    ∃key:Key,enc key=id ∧
      let ds:=key.1.map Nat.succ ++ [0] ++ key.2.flatMap (fun q=>[q.1,q.2])
      ds.length≤3*x.n+1 ∧ ds.sum≤x.n*(2*x.n+(h+1)*x.n^(2*(h+1))) := by sorry
