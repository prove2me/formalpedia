-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_native_tight_key_encoder
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.native_tight_key_encoder
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:48:50.236013+00:00
-- url     : https://prove2.me/theorems/a7c65374-f747-4653-affb-df5509ec187d
-- title:
--   A fixed native program gives injective names to arbitrary ordered tight keys
-- statement:
--   For an ordered component and its ordered boundary assignment, stream each component vertex plus one, a zero delimiter, and the successive vertex and label integers of the assignment. There is one globally injective naming of all such keys and one uniform RAM routine that writes its name. For digits d, the running time is at most A(1+length(d)+sum(d)); in particular it is independent of the magnitude of the resulting key name. The routine preserves the entire input memory and the caller registers zero through five.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.native_tight_key_encoder :
  ∃enc:Key→ℕ,Function.Injective enc ∧ ∃(A:ℕ) (cmd:Cmd),∀(x:World) (s:Store) (key:Key),
    let digits:=key.1.map Nat.succ ++ [0] ++ key.2.flatMap (fun q=>[q.1,q.2])
    Ready x s → s.imem (inputCell 6 0)=(digits.length:ℤ) →
    (∀j (hj:j<digits.length),s.imem (inputCell 7 j)=((digits[j]:ℕ):ℤ)) →
    ∃t z,Executes x.dist cmd s t z ∧ z≤A*(1+digits.length+digits.sum) ∧ t.imem=s.imem ∧
      (∀j<6,t.ptrs j=s.ptrs j) ∧ t.ptrs 6=(enc key:ℤ) := by sorry
