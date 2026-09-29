-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_substitution_y_eq_one_sub_x
-- name    : RossSolandGAP.Bound.substitution_y_eq_one_sub_x
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:10:46.52018+00:00
-- url     : https://prove2.me/theorems/a588ecf5-138e-48c4-a441-bd271877c06f
-- title:
--   §2, p. 96 — the substitution y_ij = 1 − x_ij and p_j = c_2j − c_1j
-- statement:
--   Let $m\ge2$, let $j\mapsto i_j$ be a cheapest-agent selection, $J_i=\{j:i_j=i\}$, $d_i=\sum_{j\in J_i}r_{ij}-b_i$, $p_j=\min_{k\ne i_j}(c_{kj}-c_{i_jj})$ and $c_{2j}=\min_{k\ne i_j}c_{kj}$. Fix an agent $i$ and a vector $(v_j)_{j\in J}$ with $v_j=0$ whenever $i_j\ne i$. Then:
--
--   1. $p_j=c_{2j}-c_{1j}$ for every task $j$, where $c_{1j}=c_{i_jj}$ is the smallest cost of task $j$;
--   2. agent $i$'s part of the (PR$_\lambda$) objective at $\lambda=c_2$ becomes, under $y_{ij}=1-v_j$, the (PK$_i$) objective shifted by a constant:
--   $$
--   \sum_{j\in J}(c_{ij}-c_{2j})v_j=-\sum_{j\in J_i}p_j+\sum_{j\in J_i}p_j(1-v_j);
--   $$
--   3. $v$ satisfies agent $i$'s resource constraint if and only if $y=1-v$ satisfies the (PK$_i$) constraint:
--   $$
--   \sum_{j\in J}r_{ij}v_j\le b_i\iff d_i\le\sum_{j\in J_i}r_{ij}(1-v_j).
--   $$
--
--   These are the first two observations of the paper's verification of its principal result.
--
--   **Formalization Note** The Lagrangean objective at $\lambda=c_2$ is $\sum_jc_{2j}+\sum_i\sum_j(c_{ij}-c_{2j})x_{ij}$; "agent $i$'s part" is the inner sum. Agents and tasks are 0-based.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 96, §2, second paragraph, second sentence (first two observations)

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem substitution_y_eq_one_sub_x {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m) (v : Fin n → ℝ)
    (hv : ∀ j, a j ≠ i → v j = 0) :
    (∀ j, pen hm c a j = c2 hm c a j - c (a j) j) ∧
    ∑ j, (c i j - c2 hm c a j) * v j =
      -(∑ j ∈ Jset a i, pen hm c a j) + ∑ j ∈ Jset a i, pen hm c a j * (1 - v j) ∧
    (∑ j, r i j * v j ≤ b i ↔ dgap r b a i ≤ ∑ j ∈ Jset a i, r i j * (1 - v j)) := by sorry

end RossSolandGAP.Bound
