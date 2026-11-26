-- Prove2me | Theorems.Thm_TargetedSamplers_Structured_StackMachine_fields_call
-- name    : TargetedSamplers.Structured.StackMachine.fields_call
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:43:01.256138+00:00
-- url     : https://prove2.me/theorems/8e9f073f-8755-474a-b1c6-fb2156cd4270
-- title:
--   Calling a polynomial-time binary function from fixed-width RAM fields
-- statement:
--   Let $f\colon\mathbb N\to\mathbb N$ have a polynomial-time binary stack-machine implementation. Fix $r\geq1$. A register bank contains $r$ words $x_i<2^w$ and the radix $2^w$. Write
--
--   $$z=2^{rw}+\sum_{i=0}^{r-1}x_i\,2^{iw}.$$
--
--   There exist a fixed workspace boundary and polynomials $Q,S$ such that a subroutine at each admissible bank executes on every choice of tapes. For every ambient word bound $b\geq Q(w)$ that the initial store satisfies, it uses at most $S(b)$ primitive steps, maintains the bound $b$, and returns $f(z)$ in register zero. It preserves the output string and every caller cell at or above the reserved boundary in the bank address representation.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_LogCostRAM_StructuredExecution
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

open TargetedSamplers TargetedSamplers.Structured
open Word BinaryStack NumericFields
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

theorem TargetedSamplers.Structured.StackMachine.fields_call (f : ℕ → ℕ) (poly : Poly f) (count : ℕ) (hn : 1 ≤ count) :
    ∃ (floor : ℕ) (cmd : ℕ → Cmd) (width steps : Polynomial ℕ), ∀ (bank w : ℕ) (xs : List ℕ)
      (len : xs.length=count) (valid : ∀ x∈xs,x < 2^w) (τ : Tapes) (s : Store) (b : ℕ),
      floor ≤ bank → width.eval w ≤ b → s.Fits b → s.mem (cell (bank+count))=2^w →
      (∀ i (hi : i < count), s.mem (cell (bank+i))=xs[i]'(by omega)) →
      ∃ t k, Exec τ (fun u => u.Fits b) (cmd bank) s t k ∧ k ≤ steps.eval b ∧ t.mem 0=f (pack w xs) ∧
        t.out=s.out ∧ ∀ i ≥ floor, t.mem (cell i)=s.mem (cell i) := by sorry
