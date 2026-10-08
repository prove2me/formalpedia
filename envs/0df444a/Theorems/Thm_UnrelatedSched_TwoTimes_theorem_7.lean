-- Prove2me | Theorems.Thm_UnrelatedSched_TwoTimes_theorem_7
-- name    : UnrelatedSched.TwoTimes.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:20:52.831753+00:00
-- url     : https://prove2.me/theorems/f1f4e718-57c7-4a78-9f13-a40ad4577b55
-- title:
--   Theorem 7 — with times in $\{p,q\}$, $\gcd(p,q)=1$, a $q$-dimensional matching exists iff a schedule has makespan $\le pq$
-- statement:
--   Let $p$ and $q$ be relatively prime natural numbers with $0<p<q$. Let $U$ be a ground set of $qn$ elements and $S_1,\dots,S_m$ subsets of $U$ with $|S_i|=q$ for every $i$. Build the scheduling instance on $m$ unrelated machines in which machine $i$ corresponds to $S_i$, there are $qn$ element jobs (one per $u\in U$) and $p(m-n)$ dummy jobs, an element job $u$ takes $p$ time units on machine $i$ if $u\in S_i$ and $q$ time units otherwise, and every dummy job takes $q$ time units on every machine. Then
--
--   1. every processing time of the instance lies in $\{p,q\}$, and
--   2. $$\exists\ \text{schedule } \sigma \text{ with } C_{\max}(\sigma)\le pq \iff \exists\, F'\subseteq\{1,\dots,m\}:\ |F'|=n,\ \bigcup_{i\in F'}S_i=U .$$
--
--   The paper states Theorem 7 as: the minimum makespan problem on unrelated parallel machines is NP-hard in the case that all $p_{ij}\in\{p,q\}$ with $p<q$, $2p\ne q$. Its proof assumes without loss of generality that $p$ and $q$ are relatively prime and reduces $q$-dimensional matching to the scheduling problem by exactly this construction; the equivalence above is what the proof establishes, and it is what is formalized. Together with Theorem 6 ($p_{ij}\in\{1,2\}$ is polynomially solvable) it classifies the complexity of the cases with two processing times.
--
--   **Formalization Note** NP-hardness is not formalized. The general case $\gcd(p,q)=g>1$ is the paper's "without loss of generality": dividing all times by $g$ divides every makespan by $g$; it is not part of the statement. The hypothesis $2p\ne q$ is dropped: the reduction does not use it (with coprime $p<q$ it only excludes $p=1$, $q=2$, where $q$-dimensional matching is bipartite matching and the decision problem is easy), so the statement is stronger. The q-partite structure of $q$-dimensional matching is not imposed, which contains the q-partite case. Ground set `Fin (q * n)`, jobs `Fin (q * n + p * (m - n))`, and natural-number subtraction gives no dummy jobs when $m<n$, where both sides are false for $n\ge1$.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 8, Theorem 7; proof pp. 8-9

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoTimes_Theorem7Instance

open MatousekLP.Scheduling

namespace UnrelatedSched.TwoTimes

/-- Theorem 7 (Lenstra, Shmoys, Tardos, CWI Report OS-R8714 (1987), p. 8; proof pp. 8–9), in the
form its proof establishes, for relatively prime `0 < p < q` (the paper's "without loss of
generality"): the scheduling instance `twoTimes p q n S` built from a family `S` of `m` `q`-subsets
of a ground set of `qn` elements has all processing times in `{p, q}`, and it has a schedule with
makespan at most `p * q` if and only if `S` has a matching. "NP-hard" is not formalized, and the
hypothesis `2p ≠ q` of the paper, which the reduction does not use, is dropped. -/
theorem theorem_7 {p q m n : ℕ} (hp : 0 < p) (hpq : p < q) (hcop : Nat.Coprime p q)
    (S : Fin m → Finset (Fin (q * n))) (hS : ∀ i, (S i).card = q) :
    (∀ i j, twoTimes p q n S i j = p ∨ twoTimes p q n S i j = q) ∧
      ((∃ σ : Fin (q * n + p * (m - n)) → Fin m,
          makespan (fun i j => (twoTimes p q n S i j : ℝ)) σ ≤ (p * q : ℝ)) ↔
        ∃ F' : Finset (Fin m), IsQMatching S F') := by sorry

end UnrelatedSched.TwoTimes
