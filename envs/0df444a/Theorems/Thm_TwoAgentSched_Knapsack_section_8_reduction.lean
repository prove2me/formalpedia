-- Prove2me | Theorems.Thm_TwoAgentSched_Knapsack_section_8_reduction
-- name    : TwoAgentSched.Knapsack.section_8_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:56.65173+00:00
-- url     : https://prove2.me/theorems/850392d2-921c-4f24-b2de-ec4ea8eb8885
-- title:
--   §8 — with all B due dates equal to $Q$ and $Q'=0$, $\sum U^B_i\le Q'$ is the same as $C^B_{\max}\le Q$
-- statement:
--   Consider a two-agent single-machine instance (agent $A$ with processing times $p^A_h$ and weights $w^A_h$, agent $B$ with processing times $p^B_k$), a threshold $Q_A$ for agent $A$'s total weighted completion time, and a number $Q$. Give every $B$-job the due date $d^B_k=Q$ and put $Q'=0$. Then for every sequence $\sigma$ of all jobs,
--
--   $$\Bigl(\sum_hw^A_hC^A_h(\sigma)\le Q_A\ \text{ and }\ \sum_kU^B_k(\sigma)\le 0\Bigr)\iff\Bigl(\sum_hw^A_hC^A_h(\sigma)\le Q_A\ \text{ and }\ C^B_{\max}(\sigma)\le Q\Bigr).$$
--
--   That is, a feasible solution of $1\|\sum w_iC^A_i:\sum U^B_i\le Q'$ for this instance is a feasible solution of $1\|\sum w_iC^A_i:C^B_{\max}\le Q$, and vice versa. This is how §8 transfers the NP-hardness of Theorem 5.2 to $1\|\sum w_iC^A_i:\sum U^B_i$.
--
--   **Formalization Note** $C^B_{\max}\le Q$ is written as $C^B_k\le Q$ for every $B$-job, and $J^B_k$ is late iff $C^B_k>d^B_k$. The statement is the encoding-free equivalence on the paper's construction; the corresponding polynomial-time reduction between languages is not stated.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 237, §8

import Mathlib
import Definitions.Def_TwoAgentSched_Knapsack_Model

namespace TwoAgentSched.Knapsack

/-- §8 (Agnetis et al. 2004, p. 237): for the same jobs, giving every B-job the due date `Q` and
taking `Q' = 0`, a sequence is feasible for `1‖∑ w_iC^A_i ≤ Q_A, ∑ U^B_i ≤ 0` iff it is feasible
for `1‖∑ w_iC^A_i ≤ Q_A, C^B_max ≤ Q`. -/
theorem section_8_reduction (I : Instance) (QA Q : ℝ) (l : List (Fin I.nA ⊕ Fin I.nB)) :
    I.MeetsU QA (fun _ => Q) 0 l ↔ I.Meets QA Q l := by sorry

end TwoAgentSched.Knapsack
