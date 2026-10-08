-- Prove2me | Theorems.Thm_TwoAgentSched_TotalTotal_theorem_9_2
-- name    : TwoAgentSched.TotalTotal.theorem_9_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:10.7936+00:00
-- url     : https://prove2.me/theorems/6a84217c-bc18-4142-bf54-2bb28c32b9aa
-- title:
--   Theorem 9.2 — $1\|\sum C^A_i : \sum C^B_i$ is binary NP-hard (PARTITION reduces to it)
-- statement:
--   **Theorem 9.2** (Agnetis, Mirchandani, Pacciarelli and Pacifici 2004). The two-agent problem $1\|\sum C^A_i : \sum C^B_i$, with one machine and two agents each minimising its own total completion time, is binary NP-hard.
--
--   The statement formalised is the reduction the paper gives: PARTITION (Problem 9.1) is polynomial-time many-one reducible to the recognition problem $1\|\sum C^A_i\le Q_A,\ \sum C^B_i\le Q_B$,
--
--   $$\text{PARTITION}\ \le_p\ 1\|\textstyle\sum C^A_i\le Q_A,\ \sum C^B_i\le Q_B ,$$
--
--   where both languages consist of binary codes of yes-instances over a four-letter alphabet. That is, there is a function $f$ on strings, computable by a Turing machine in time polynomial in the input length, such that a string is the code of a PARTITION yes-instance (a list of nonnegative integers that can be split into two parts of equal sum) iff $f$ of it is the code of a two-agent instance with thresholds $Q_A,Q_B\in\mathbb N$ for which some sequence of all jobs has $\sum_hC^A_h\le Q_A$ and $\sum_kC^B_k\le Q_B$.
--
--   Since PARTITION is NP-complete (Karp 1972), this shows that the two-agent problem is NP-hard under binary encoding of the numbers.
--
--   **Formalization Note** Polynomial-time computability and many-one reducibility are the published `CookPvsNP.PolyReducible` (Cook's Definition 3, one-tape Turing machines); PARTITION and the codes are the published `ProjSchedTW.Complexity.partitionLang` and `encNats`, in which sizes are natural numbers and $0$ is allowed. Neither the NP-completeness of PARTITION nor the membership of the target problem in NP ("Membership in NP is trivial") is part of the statement. The target language allows any numbers of jobs and any processing times; identical job sets are a feature of the paper's construction only. The paper's thresholds $T/2$ are half-integers when $P$ is odd, while the target language has thresholds in $\mathbb N$. The paper's construction as printed is correct only for PARTITION instances without repeated values (see the equivalence milestone); a reduction for all instances must handle repeated values. Strings that are not codes of PARTITION instances must be mapped outside the target language.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 237, Theorem 9.2 (Problem 9.1: p. 237; recognition problem: p. 232)

import Mathlib
import Definitions.Def_TwoAgentSched_TotalTotal_Model

namespace TwoAgentSched.TotalTotal

open CookPvsNP ProjSchedTW.Complexity

/-- Theorem 9.2 (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, p. 237):
`1‖∑ C^A_i : ∑ C^B_i` is binary NP-hard, in the form proved there: PARTITION (Problem 9.1) is
polynomial-time many-one reducible to the recognition problem
`1‖∑ C^A_i ≤ Q_A, ∑ C^B_i ≤ Q_B`, both languages coded in binary over `BSym`. -/
theorem theorem_9_2 : PolyReducible partitionLang targetLang := by sorry

end TwoAgentSched.TotalTotal
