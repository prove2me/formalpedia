-- Prove2me | Theorems.Thm_TopkisRation_Levels_eq_6
-- name    : TopkisRation.Levels.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:41.804597+00:00
-- url     : https://prove2.me/theorems/09f786f7-367f-44fa-8320-2ff44dfb9d02
-- title:
--   (6), p. 165 — f_t(z, B) is the minimum of f_t(w; z, B) over w ∈ [(z − B^{(1)})⁺, z]
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $1\le t\le k$, $z\ge0$ and $B\ge0$, and write $B^{(1)}=\sum_jB^j$. Then
--
--   $$
--   f_t(z,B)=\min_{w\in[(z-B^{(1)})^+,\,z]}f_t(w;z,B), \tag{6}
--   $$
--
--   where $f_t(w;z,B)$ is the cost (4) of issuing exactly $z-w$ units in interval $t$: the infimum over $w$ equals $f_t(z,B)$ and is attained.
--
--   Together with Lemma 4 this reduces the choice of the optimal vector $u$ in (1) to the choice of the single number $w$, the stock level after rationing.
--
--   **Formalization Note.** The statement asserts both the equality with the real `sInf` and the existence of a minimizing $w$, which is what "min" means.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 165, (6)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split

namespace TopkisRation.Levels

theorem eq_6 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B) :
    M.f t z B = sInf ((fun w => M.fw t w z B) '' Set.Icc (max (z - ∑ j, B j) 0) z) ∧
    ∃ w ∈ Set.Icc (max (z - ∑ j, B j) 0) z, M.fw t w z B = M.f t z B := by sorry

end TopkisRation.Levels
