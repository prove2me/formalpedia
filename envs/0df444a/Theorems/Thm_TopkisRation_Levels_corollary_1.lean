-- Prove2me | Theorems.Thm_TopkisRation_Levels_corollary_1
-- name    : TopkisRation.Levels.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:43.864976+00:00
-- url     : https://prove2.me/theorems/efe4759e-b177-4594-b876-595c00dbc809
-- title:
--   Corollary 1, p. 165 — some optimal u leaves no demand of class i > j unsatisfied whenever u^j < B^j
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $1\le t\le k$, $z\ge0$ and $B\ge0$. There is a feasible vector $u$ ($0\le u\le B$, $\mathbf 1\cdot(B-u)\le z$) that attains the minimum in (1),
--
--   $$
--   f_t(z,B)=p_t\cdot u+h_t\big(z-\mathbf 1\cdot(B-u)\big)+g_{t-1}\big(z-\mathbf 1\cdot(B-u),\,a_tu\big),
--   $$
--
--   and satisfies: $u^j<B^j$ implies $u^i=0$ for all $i>j$.
--
--   So some optimal rationing decision serves a class only after every more important class has been fully served.
--
--   **Formalization Note.** "Optimal feasible" is read as attaining $f_t(z,B)$ in (1); by Lemma 2 that value is the minimum of the bracket.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 165, Corollary 1

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem corollary_1 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    ∃ u ∈ feasible z B, M.f t z B = M.obj t (M.g (t - 1)) z B u ∧
      ∀ j i : Fin n, u j < B j → j < i → u i = 0 := by sorry

end TopkisRation.Levels
