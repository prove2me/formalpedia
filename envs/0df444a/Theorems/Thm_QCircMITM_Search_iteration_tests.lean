-- Prove2me | Theorems.Thm_QCircMITM_Search_iteration_tests
-- name    : QCircMITM.Search.iteration_tests
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:13.946264+00:00
-- url     : https://prove2.me/theorems/ac80a5a9-64b9-40b5-9ae6-1d2c646998ed
-- title:
--   §3, p. 6 — iteration i of MITM-factor tests depth 2i − 1, then depth 2i
-- statement:
--   Let $V \subseteq U(2^n)$ be a finite set of unitaries (standing for $\mathcal V_{n,\mathcal G}$), $U$ a unitary and $i \ge 1$. Consider iteration $i$ of MITM-factor, which tests $S_{i-1}^\dagger U \cap S_i \neq \emptyset$ and then $S_i^\dagger U \cap S_i \neq \emptyset$.
--
--   1. The iteration returns nothing if and only if $U \notin S_{2i-1}$ and $U \notin S_{2i}$.
--   2. If it returns a circuit $c$, then every layer of $c$ lies in $V$, $c$ implements $U$, and
--   $$|c| = \begin{cases} 2i-1 & \text{if } U \in S_{2i-1},\\ 2i & \text{if } U \notin S_{2i-1}.\end{cases}$$
--
--   In words: the first test succeeds exactly when $U$ has a circuit of depth $2i-1$, the second exactly when it has one of depth $2i$, and the returned circuit has that depth.
--
--   **Formalization Note.** $|c|$ is the length of the list $c$ of layers. The statement holds for every finite set of unitaries $V$.
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, p. 6, §3 (paragraph after the MITM-factor pseudocode)

import Mathlib
import Definitions.Def_QCircMITM_Search_Algorithm

namespace QCircMITM.Search

theorem iteration_tests {n : ℕ} (V : Finset (Unitary n)) (U : Unitary n) (i : ℕ) (hi : 1 ≤ i) :
    (mitmStep V U i = none ↔ U ∉ S V (2 * i - 1) ∧ U ∉ S V (2 * i)) ∧
    ∀ c, mitmStep V U i = some c →
      (∀ W ∈ c, W ∈ V) ∧ c.prod = U ∧
      (U ∈ S V (2 * i - 1) → c.length = 2 * i - 1) ∧
      (U ∉ S V (2 * i - 1) → c.length = 2 * i) := by sorry

end QCircMITM.Search
