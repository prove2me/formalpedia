-- Prove2me | Theorems.Thm_StableMSR_Recovery_Compiler_TupleEnumeration_bounded_subset_enumerator_program
-- name    : StableMSR.Recovery.Compiler.TupleEnumeration.bounded_subset_enumerator_program
-- status  : Proved
-- author  : @lreyzin
-- created : 2026-11-14T19:40:26.42312+00:00
-- url     : https://prove2.me/theorems/5aed468d-db4b-49eb-8a99-80d006a36780
-- title:
--   A fixed-width bounded-subset encoding program with polynomial charged time
-- statement:
--   For every fixed width $w\ge0$, there is one deterministic program, chosen before the input size and oracle, with exactly $7w+7$ instructions. On every input size $n\ge0$ and integer input parameter $k$, it halts after at most
--
--   $$(8w+2)(n+1)^w+5$$
--
--   charged interpreter steps, making no distance queries and reading no random tape. It reads $n$ from the standard input memory and writes a positive-address scratch catalog beginning at address $2$. Reading the $(n+1)^w$ fixed-width records gives exactly the lexicographic list of all words of length $w$ over digits $0,\ldots,n$. With zero treated as padding and digit $v+1$ representing vertex $v$, the decoded records cover exactly all subsets of $\mathrm{Fin}(n)$ of cardinality at most $w$; different records may decode to the same subset. The output pointer ends at $2+(w+1)(n+1)^w$. Input cells $0,1$, real memory, and integer memory outside the catalog are preserved, and charged work equals the executed instruction count.
--
--   The theorem includes $w=0$ and $n=0$. It is a concrete internal enumeration kernel in the recovery interpreter, not the complete clustering algorithm or the canonical negative-address clustering-output format.
-- source:
--   Concrete nested-loop word enumeration and padded-subset encoding developed for the Exact Sum-of-Radii Clustering under Any Constant Stability mission; verified using compiler_execution_exact https://prove2.me/theorems/b5dceca8-b6ae-4872-9eda-300198cc4b1a and the canonical recovery interpreter.

import Definitions.Def_StableMSR_BoundedWordCatalog
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.TupleEnumeration

theorem StableMSR.Recovery.Compiler.TupleEnumeration.bounded_subset_enumerator_program (w : ℕ) :
    ∃ P : MinSumFPT.Program, DeterministicProgram P ∧ P.length = 7*w+7 ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ),
        ∃ steps ≤ (8*w+2)*(n+1)^w+5,
          let result := execute P n k d steps
          result.halted = true ∧ result.work = steps ∧
          result.queries = 0 ∧ result.tapePos = 0 ∧
          result.cfg.ptrs (w+1) = 2+((w+1)*(n+1)^w : ℕ) ∧
          result.imem 0 = (n : ℤ) ∧ result.imem 1 = (k : ℤ) ∧
          catalogWords n w result.imem = BoundedSubsetWords.words n w ∧
          (∀ S : Finset (Fin n), S.card ≤ w ↔
            ∃ j < (n+1)^w,
              BoundedSubsetWords.decode n
                (readWord w result.imem (2+((w+1)*j : ℕ))) = S) ∧
          (∀ a : ℤ, a < 2 ∨ 2+((w+1)*(n+1)^w : ℕ) ≤ a →
            result.imem a = (initialStore n k).imem a) ∧
          result.cfg.mem = (initialStore n k).mem := by sorry
