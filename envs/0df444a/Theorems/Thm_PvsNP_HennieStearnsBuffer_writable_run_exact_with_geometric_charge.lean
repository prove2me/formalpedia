-- Prove2me | Theorems.Thm_PvsNP_HennieStearnsBuffer_writable_run_exact_with_geometric_charge
-- name    : PvsNP.HennieStearnsBuffer.writable_run_exact_with_geometric_charge
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T17:18:54.339092+00:00
-- url     : https://prove2.me/theorems/f836f0ee-f5ae-5cd1-afa2-14d4a97da03a
-- title:
--   Exact writable dyadic tape replay with a geometric cleanup bound
-- statement:
--   Consider a two-sided writable tape over an alphabet $A$ with a distinguished blank symbol. An instruction writes a symbol at the head and then moves left, stays in place, or moves right. Both sides are initially blank. A deterministic buffer represents the tape by a center symbol and a finite sequence of layers, indexed from $0$. In layer $i$, each side holds zero, one, or two blocks of size $2^i$, and the two sides together hold exactly two such blocks. The represented view treats all unallocated cells as blank.
--
--   A move selects the first layer that contains a symbol on the side being entered and redistributes the intervening layers. If the current layers do not contain such a symbol, the buffer first allocates a balanced blank layer. Each cleanup records its order $i$ and whether the selected layer is unbalanced afterward. A stay performs no cleanup.
--
--   For an instruction list of length $T$, ordinary execution and buffered execution have the same final tape view. The layer capacities are preserved. The cleanup schedule starts with no unbalanced layers and has at most $T$ events. If the recorded cleanup orders are $i_1,\dots,i_m$, then
--
--   $$
--   \sum_{j=1}^{m} 2^{i_j} \le T\,\operatorname{size}(T).
--   $$
--
--   Here $\operatorname{size}$ is the binary length, with $\operatorname{size}(0)=0$. The bound quantifies the geometric charge of a writable buffer even when the head repeatedly changes direction. It isolates the storage and scheduling part of multitape simulation.
-- source:
--   F. C. Hennie and R. E. Stearns, Two-Tape Simulation of Multitape Turing Machines, JACM 13(4), 533–546 (1966), §3, storage rearrangement and Lemmas 1–6, https://www.cs.toronto.edu/tss/files/papers/HennieStearns66.pdf. The submitted statement specifies the writable-buffer semantics and geometric charge independently of physical compilation.

import Definitions.Def_HennieStearnsWritableBuffer

set_option autoImplicit false

open PvsNP.HennieStearnsBuffer

theorem PvsNP.HennieStearnsBuffer.writable_run_exact_with_geometric_charge {A : Type} (blank : A) (instructions : List (A × Turn)) :
    let initial := blankBuffer blank
    let result := runBuffer blank initial instructions
    FitsFrom 0 result.1.layers ∧
      glimpse blank result.1 = runSnapshot (glimpse blank initial) instructions ∧
      physicalSchedule (fun _ => false) result.2 ∧
      result.2.length ≤ instructions.length ∧
      bill (result.2.map Prod.fst) ≤ instructions.length*instructions.length.size := by sorry
