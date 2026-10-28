-- Prove2me | Theorems.Thm_QPurityAmp_Choi_feasible_rows_ordered
-- name    : QPurityAmp.Choi.feasible_rows_ordered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:32.012979+00:00
-- url     : https://prove2.me/theorems/f351dc63-9268-441e-a4f5-6d1ff2be49e2
-- title:
--   p. 21, below Eq. (S28) — [µ_i] ⪯ [µ_j] whenever i ≤ j, for feasible rows i, j
-- statement:
--   Let $\varsigma$ be a Young diagram with $n$ boxes and at most $d$ rows, and let $i\le j$ be feasible rows of $\varsigma$. Then
--   $$[\mu_i]\preceq[\mu_j],$$
--   where $[\mu_i]=\varsigma-e_i$ and $\preceq$ is the dominance order of Eq. (S27): removing a box from a higher row gives a diagram lower in dominance order.
--
--   With Eqs. (S26) and (S28), this shows that the smallest feasible row $i^*$ has the largest coefficient $c'_{i^*}$.
--
--   **Formalization Note** Stated for the shifted diagrams $\nu_i=\mu_i+(1^d)$, which have no negative rows; adding $(1^d)$ to both diagrams adds the same amount to each partial sum, so the order is unchanged.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 21, text below Eq. (S28)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open QAlgorithms.Schur

/-- p. 21, below Eq. (S28): [µ_i] ⪯ [µ_j] whenever i ≤ j, for feasible rows i, j of ς. With
the determinant shift ν_i = µ_i + (1^d), stated for ν_i and ν_j (adding (1^d) to both sides
does not change the dominance order). -/
theorem feasible_rows_ordered {d n : ℕ} (vs : Partition d n)
    (i j : {i : Fin d // IsFeasibleRow vs i}) (hij : i.val ≤ j.val) :
    DomLE (shiftedYD vs i) (shiftedYD vs j) := by sorry

end QPurityAmp.Choi
