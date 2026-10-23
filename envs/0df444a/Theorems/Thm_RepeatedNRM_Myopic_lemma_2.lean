-- Prove2me | Theorems.Thm_RepeatedNRM_Myopic_lemma_2
-- name    : RepeatedNRM.Myopic.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:00.07264+00:00
-- url     : https://prove2.me/theorems/0e955a2c-11d1-4dd0-a124-e7c60bcc8d2e
-- title:
--   Lemma 2, p. ec3 — the class of an under-spending customer exhausts the supply of every product it desires
-- statement:
--   Let $x$ be a myopic allocation at budgets $\mathbf b_1\in[0,1]^m$, i.e. an optimal solution of (7), and let $A_1,\dots,A_m$ be the characteristic sets of Assumption 2. Suppose customer $j$ under-spends on its desired products:
--   $$\sum_{i\in A_j}p_{ij}x_{ij}<b_{j,1}.$$
--   Let $C_j$ be the class of Definition 2: the smallest set of customers containing $j$ such that every customer receiving a positive amount of a product desired by a member is a member. Then every product desired by a member of $C_j$ is fully allocated to $C_j$:
--   $$\sum_{l\in C_j}x_{il}=s_i\qquad\text{for all } i\in\bigcup_{l\in C_j}A_l.$$
--
--   Otherwise an augmenting path from $j$ would raise revenue. The lemma is the combinatorial core of Proposition 4.
--
--   Differences from the source:
--   - reading: the standing assumption $b_{j,t}\in[0,1]$ (p. 9), not repeated in the statement → hypothesis that the initial budgets lie in $[0,1]$; reason: the paper's standing assumption made explicit; later budgets stay in $[0,1]$ because $\varphi_j$ maps $[0,1]^2$ into $[0,1]$
--   - reading: "the myopic policy" $\{\mathbf x^{MY}_t\}$ → every trajectory whose allocation in each period is an optimal solution of (7) at the current budgets; reason: (7) can have several optimal solutions; the statement is made for every selection, the stronger of the two readings
--   - reading: the class $C_j$ by the printed iteration $C_j\leftarrow D_j(C_j)$ from $\{j\}$, with "$k\in\{1,\dots,n\}$" → the least set of customers containing $j$ and closed under "receives a positive amount of a product desired by a member"; reason: read as a replacement, the iteration can drop $j$ and need not stabilise; the cumulative reading is the set with the property stated under Definition 2, and it is the larger class, so the claim covers more products; $\{1,\dots,n\}$ is a typo for the customers $\{1,\dots,m\}$
--   - reading: $A_j$, the characteristic sets of Assumption 2 (the lemma names no assumption) → hypothesis Assumption 2 holds with sets $A_j$ for some $\gamma\in[0,1]$; reason: $A_j$ is only defined through Assumption 2; $\gamma$ is arbitrary
--   - encoding: Assumption 2(i), which divides by $p_{ij}$ for $i\in A_j$ → Assumption 2 includes $p_{ij}>0$ for $i\in A_j$; reason: the ratios $v_{ij}/p_{ij}$ are undefined otherwise; this excludes only undefined cases
--   - encoding: $\min_{i\in A_j} v_{ij}/p_{ij} - 1 \ge (1-\gamma)(\max_{i\in A_j} v_{ij}/p_{ij} - 1)$ → $v_{ij}/p_{ij} - 1 \ge (1-\gamma)(v_{kj}/p_{kj} - 1)$ for all $i,k\in A_j$; reason: equivalent for nonempty $A_j$; for empty $A_j$ the min and max are undefined and the pairwise clause is vacuous
-- source:
--   Calmon, Ciocan & Romero, accepted manuscript (TSpace), p. ec3, Lemma 2 and Definition 2

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Proof

namespace RepeatedNRM.Myopic

theorem lemma_2 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h2 : Assumption2 I A γ) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin I.n → Fin I.m → ℝ) (hx : IsMyopicAlloc I b1 x) (j : Fin I.m)
    (hj : ∑ i ∈ A j, I.p i j * x i j < b1 j) :
    ∀ i, (∃ l ∈ customerClass I A x j, i ∈ A l) →
      ∑ l ∈ customerClass I A x j, x i l = I.s i := by sorry
end RepeatedNRM.Myopic
