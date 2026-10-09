-- Prove2me | Theorems.Thm_RamanujanNotebooks_entry_40_12_13
-- name    : RamanujanNotebooks.entry_40_12_13
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T15:05:48.023851+00:00
-- url     : https://prove2.me/theorems/27f1226c-783c-4bfa-bc42-4ac553787c5e
-- title:
--   Well-poised hypergeometric evaluation 13
-- statement:
--   For complex n,x with Re(x+n)>1 and with every lower rising factorial (n/2)_k, (n)_k and (x+n+1)_k nonzero, the series n·₄F₃(n/2+1,1,1,−x; n/2,n,x+n+1; 1) converges absolutely to (n−1)(x+n)/(x+n−1). Differs from the printed source: the usual exclusion of zero lower rising factorials, implicit in the hypergeometric notation, is explicit here.
--
--   **Discrepancy from the printed source.** the usual exclusion of zero lower rising factorials, implicit in the hypergeometric notation, is explicit here.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part IV (Springer, 1994), Chapter 40, Entry 12_13, p. 407.

import Mathlib
import Definitions.Def_RamanujanNotebooks_shared_hypPFQTerm
import Definitions.Def_RamanujanNotebooks_shared_shiftedFactorial

namespace RamanujanNotebooks
theorem entry_40_12_13 (n x : ℂ) (h : 1 < (x + n).re)
    (hn : ∀ k : ℕ, shiftedFactorial (n / 2) k ≠ 0)
    (hd : ∀ k : ℕ, shiftedFactorial (x + n + 1) k ≠ 0)
    (hnn : ∀ k : ℕ, shiftedFactorial n k ≠ 0) :
    HasSum (fun k : ℕ => n * hypPFQTerm [n / 2 + 1, 1, 1, -x] [n / 2, n, x + n + 1] (1) k) ((n - 1) * (x + n) / (x + n - 1)) := by sorry
end RamanujanNotebooks
