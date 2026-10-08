-- Prove2me | Theorems.Thm_QLLL_SAT_counting_clauseEvent_ge
-- name    : QLLL.SAT.counting_clauseEvent_ge
-- status  : Proved
-- author  : @sattath
-- created : 2026-10-06T17:46:17.003347+00:00
-- url     : https://prove2.me/theorems/2df9ad49-936c-4bdc-a350-506f9f619692
-- title:
--   A clause on $k$ distinct variables is satisfied by at least a $1 - 2^{-k}$ fraction of assignments
-- statement:
--   A clause is a disjunction of literals over boolean variables, and an assignment satisfies it if at least one literal evaluates to true. Let $c$ be a clause over the variables $x_1, \dots, x_V$ that involves exactly $k$ distinct variables. Then, for an assignment $a$ chosen uniformly from $\{0,1\}^{V}$,
--   $$\Pr\big[a \text{ satisfies } c\big] \ \ge\ 1 - \frac{1}{2^{k}}.$$
--
--   This is the probability estimate in the derivation of Corollary 2 of Ambainis, Kempe and Sattath from the symmetric local lemma: a random assignment violates a $k$-clause with probability at most $2^{-k}$.
--
--   **Formalization Note** The probability is the uniform counting valuation on `Fin V → Bool`.
-- source:
--   A. Ambainis, J. Kempe, O. Sattath, A Quantum Lovász Local Lemma, J. ACM 59(5):24 (2012), arXiv:0911.1696 (numbering of the arXiv version), proof of Corollary 2 (the estimate $p = 2^{-k}$)

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Classical_KSAT
import Mathlib
import Std.Sat.CNF

open QLLL
open QLLL.SAT
open Finset Std.Sat
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
variable {V : ℕ}

theorem QLLL.SAT.counting_clauseEvent_ge {c : CNF.Clause (Fin V)} {k : ℕ}
    (hk : (clauseVars c).card = k) :
    1 - 1 / 2 ^ k ≤ counting (Asg V) (clauseEvent c) := by sorry
