-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_partitionProject_feasible_iff
-- name    : ProjSchedTW.Complexity.partitionProject_feasible_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:08:59.227426+00:00
-- url     : https://prove2.me/theorems/0e6d4c3c-eba3-4055-b91c-dd3cfa09ade0
-- title:
--   Proof of Theorem 2.12.1 — the PARTITION project is feasible iff the sizes split evenly
-- statement:
--   Let $s(1),\dots,s(\nu)\in\mathbb N$ with $\sum_{i\in\mathcal I}s(i)$ even, $\mathcal I=\{1,\dots,\nu\}$. Consider the project with $\nu+2$ activities of duration zero and one cumulative resource: $n=\nu$, $V=\mathcal I\cup\{0,n+1\}$,
--   $$r_0=r_{n+1}=-\tfrac12\sum_{i\in\mathcal I}s(i),\qquad r_i=s(i)\ (i\in\mathcal I),\qquad \underline R=\overline R=0,$$
--   and arcs $\langle0,n+1\rangle$ with $d^{\min}_{0,n+1}=1$, $\langle0,i\rangle$ and $\langle i,n+1\rangle$ with $d^{\min}_{0i}=d^{\min}_{i,n+1}=0$ ($i\in\mathcal I$). Then its project network is acyclic, and
--   $$\exists\,S\text{ feasible}\iff\exists\,\mathcal I'\subseteq\mathcal I:\ \sum_{i\in\mathcal I'}s(i)=\sum_{i\in\mathcal I\setminus\mathcal I'}s(i).$$
--
--   This is the correctness of the polynomial transformation from PARTITION in the proof of Theorem 2.12.1; the book remarks that the activities of $\mathcal I'$ start at time $0$ and those of $\mathcal I''$ at time $S_{n+1}\ge1$.
--
--   **Formalization Note** The book's $r_0=-\sum s(i)/2$ is an integer only for even sums, and demands are integers (p. 129); the evenness hypothesis makes that explicit (for odd sums no partition exists). Index $i\in\{1,\dots,\nu\}$ is `i - 1 : Fin ν` for the sizes and activity `i : Fin (ν + 2)`. Inventory constraints are required for every $t\ge0$.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 131, proof of Theorem 2.12.1, the PARTITION transformation ("Obviously, there is a feasible schedule if and only if …")

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_Cumulative

namespace ProjSchedTW.Complexity

/-- Proof of Theorem 2.12.1 (p. 131): the project built from PARTITION sizes `s(1), …, s(ν)`
with even total size has an acyclic network, and it has a feasible schedule iff the index set
can be split into two parts of equal total size. -/
theorem partitionProject_feasible_iff {ν : ℕ} (s : Fin ν → ℕ) (hs : Even (∑ i, s i)) :
    (partitionProject s).IsAcyclic ∧
      ((∃ S, (partitionProject s).Feasible S) ↔
        ∃ A : Finset (Fin ν), ∑ i ∈ A, s i = ∑ i ∈ Aᶜ, s i) := by sorry

end ProjSchedTW.Complexity
