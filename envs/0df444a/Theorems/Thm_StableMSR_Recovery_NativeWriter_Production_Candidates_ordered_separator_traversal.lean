-- Prove2me | Theorems.Thm_StableMSR_Recovery_NativeWriter_Production_Candidates_ordered_separator_traversal
-- name    : StableMSR.Recovery.NativeWriter.Production.Candidates.ordered_separator_traversal
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-23T23:51:38.234536+00:00
-- url     : https://prove2.me/theorems/3a17269a-bbc1-4efe-9d0e-747122c3c912
-- title:
--   Enumerating active separators in the compiler order with bounded depth
-- statement:
--   For any active set on n ordered vertices, emit the empty extension, then try the eligible next vertices in decreasing order, recursively requiring all later extensions to be larger. The depth is the separator width. The emitted list, with its full order, equals the finite compiler’s cut list and contains no duplicate separator. Counting one emission per node and all n vertex tests at each internal node costs at most (n+1)^(w+1), with no changes of order or searches through all 2^n subsets.
-- source:
--   Ravichandran and Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, Appendix A.6, pp. 21–22, https://arxiv.org/abs/2611.03547. Quantitative implementation lemma for the mission’s dense regional circuit.

import Definitions.Def_StableMSR_UnfilteredSeparatorCandidates
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries StableMSR.Recovery.WindowCSP StableMSR.Recovery.NativeWriter StableMSR.Recovery.NativeWriter.Relative StableMSR.Recovery.NativeWriter.Production StableMSR.Recovery.SingleCircuit

open StableMSR.Recovery.NativeWriter.Production.Candidates

theorem StableMSR.Recovery.NativeWriter.Production.Candidates.ordered_separator_traversal (n:ℕ) (active:ℕ→Bool) :
    let V:=fun lo:ℕ=>(List.range n).filter (fun v=>decide (lo≤v) && active v)
    ∃(walk:ℕ→ℕ→List (List ℕ)) (tests:ℕ→ℕ→ℕ),
      (∀lo,walk lo 0=[[]] ∧ tests lo 0=1) ∧
      (∀lo w,walk lo (w+1)=[]::(V lo).reverse.flatMap (fun v=>(walk (v+1) w).map (v::·)) ∧
        tests lo (w+1)=1+n+((V lo).reverse.map (fun v=>tests (v+1) w)).sum) ∧
      ∀lo w,walk lo w=TightLanguage.cuts (V lo) w ∧ (walk lo w).Nodup ∧
        tests lo w≤(n+1)^(w+1) := by sorry
