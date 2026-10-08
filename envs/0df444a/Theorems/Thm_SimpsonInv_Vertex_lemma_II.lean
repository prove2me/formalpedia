-- Prove2me | Theorems.Thm_SimpsonInv_Vertex_lemma_II
-- name    : SimpsonInv.Vertex.lemma_II
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:09.0327+00:00
-- url     : https://prove2.me/theorems/bb981581-ca1a-489c-af7a-7a05cb5e7d88
-- title:
--   LEMMA II, pp. 872–873 — every minimizer of f over D lies beyond the relative interior of a face
-- statement:
--   Let $n = m + 1$ with $m \ge 2$ variables, let $c, S_0, S_n, T_1, \dots, T_n$ be real constants and $r_1, \dots, r_n > 0$, and let $D$ and
--   $$
--   f(S_1, \dots, S_{n-1}) = c + \sum_{i=1}^{n} r_i \sqrt{S_{i-1} - S_i + T_i}
--   $$
--   be as in THEOREM I. $D$ is defined by the $2n - 1$ inequalities $S_i \ge 0$ ($1 \le i \le n-1$) and $S_{i-1} - S_i + T_i \ge 0$ ($1 \le i \le n$). If $v \in D$ minimizes $f$ over $D$, then the normals of the inequalities that hold with equality at $v$ span a space of dimension at least two.
--
--   In the paper's words, the minimum lies on the boundary of the faces of $D$, not in the relative interior of a single face; iterating this is the induction that proves THEOREM I.
--
--   **Formalization Note** "On the boundary of the 'faces'" is encoded by `tightRank ≥ 2`: at least two independent active boundary normals. This excludes a point on just one facet even when two listed inequalities define that same facet. The hypothesis $m \ge 2$ is added: with one variable the faces are points and the statement degenerates. $r_i > 0$ is from equation (8). Lean index $j$ is the paper's $S_{j+1}$.
-- source:
--   Simpson, In-Process Inventories, Operations Research 6 (1958), pp. 872–873, LEMMA II

import Mathlib
import Definitions.Def_SimpsonInv_Vertex_Setting

namespace SimpsonInv.Vertex

theorem lemma_II {m : ℕ} (c S0 Sn : ℝ) (r T : ℕ → ℝ) (hm : 2 ≤ m)
    (hr : ∀ i ∈ Finset.Icc 1 (m + 1), 0 < r i) :
    ∀ v ∈ dom (m := m) T S0 Sn,
      IsMinOn (cost c r T S0 Sn) (dom (m := m) T S0 Sn) v → 2 ≤ tightRank T S0 Sn v := by sorry

end SimpsonInv.Vertex
