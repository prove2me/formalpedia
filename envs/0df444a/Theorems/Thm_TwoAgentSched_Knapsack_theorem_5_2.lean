-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_theorem_5_2
-- name    : TwoAgentSched.Knapsack.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:53.801407+00:00
-- url     : https://prove2.me/theorems/4f4448aa-1851-4493-9a4f-dcd3ce26d678
-- title:
--   Theorem 5.2 — $1\|\sum w_iC^A_i : C^B_{\max}$ is binary NP-hard (KNAPSACK reduces to it)
-- statement:
--   **Theorem 5.2** (Agnetis, Mirchandani, Pacciarelli and Pacifici 2004). The two-agent problem $1\|\sum w_iC^A_i : C^B_{\max}$ — one machine, agent $A$ minimising its total weighted completion time while agent $B$'s makespan must not exceed a bound — is binary NP-hard.
--
--   The statement formalised is the reduction the paper gives: KNAPSACK (Problem 5.1) is polynomial-time many-one reducible to the recognition problem $1\|\sum w_iC^A_i\le Q_A,\ C^B_{\max}\le Q_B$,
--
--   $$\text{KNAPSACK}\ \le_p\ 1\|\textstyle\sum w_iC^A_i\le Q_A,\ C^B_{\max}\le Q_B ,$$
--
--   where both languages consist of binary codes of yes-instances over a four-letter alphabet. That is, there is a function $f$ on strings, computable by a Turing machine in time polynomial in the input length, such that a string is the code of a KNAPSACK yes-instance iff $f$ of it is the code of an instance with thresholds $Q_A,Q_B$ for which some sequence of all jobs has $\sum_iw^A_iC^A_i\le Q_A$ and $C^B_k\le Q_B$ for all $B$-jobs $k$.
--
--   Since KNAPSACK is NP-complete under binary encoding of the numbers (Garey and Johnson 1979), this shows that the two-agent problem is NP-hard under binary encoding.
--
--   **Formalization Note** Polynomial-time computability and many-one reducibility are the published `CookPvsNP.PolyReducible` (Cook's Definition 3, one-tape Turing machines); codes use the published `ProjSchedTW.Complexity.Encoding`. Neither the NP-completeness of KNAPSACK nor membership of the target problem in NP is part of the statement. The target language allows any numbers $n_A,n_B\ge0$ of jobs; the paper's construction uses $n_B=1$. The construction's thresholds $Q_A,Q_B$ are integers and can be negative (when $b<-\hat w\hat u$, or $W>\hat w+1$), while the target language has thresholds in $\mathbb N$: such KNAPSACK instances are no-instances and must be mapped to a no-instance of the target. KNAPSACK instances with $\sum_iw_iu_i=0$, where the paper's argument for (2) does not apply, are yes-instances iff $b\ge0$ and $\sum_{i:u_i=0}w_i\ge W$, and must likewise be mapped correctly. Strings that are not codes of KNAPSACK instances must be mapped outside the target language.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, Theorem 5.2 (recognition problem: p. 232)

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Problem51
import Definitions.Def_TwoAgentSched_Knapsack_Model

namespace TwoAgentSched.Knapsack

open CookPvsNP

/-- Theorem 5.2 (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, p. 233):
`1‖∑ w_iC^A_i : C^B_max` is binary NP-hard, in the form proved there: KNAPSACK (Problem 5.1) is
polynomial-time many-one reducible to the recognition problem
`1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q_B`, both languages coded in binary over `BSym`. -/
theorem theorem_5_2 : PolyReducible knapsackLang targetLang := by sorry

end TwoAgentSched.Knapsack
