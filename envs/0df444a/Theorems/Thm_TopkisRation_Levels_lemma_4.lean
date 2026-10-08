-- Prove2me | Theorems.Thm_TopkisRation_Levels_lemma_4
-- name    : TopkisRation.Levels.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:52:05.029986+00:00
-- url     : https://prove2.me/theorems/e3b4fca7-7313-474a-875a-b4320d45021f
-- title:
--   Lemma 4, p. 165 — the priority vector u(z − w, B) of (5) is feasible for (4) and minimizes it
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $1\le t\le k$, $z\ge0$, $B\ge0$ and $w\in[(z-B^{(1)})^+,z]$. Let $U=\{u:\ 0\le u\le B,\ \mathbf 1\cdot(B-u)=z-w\}$ be the constraint set of (4), and let $u(z-w,B)$ be the vector (5), $u^j(z-w,B)=(B^{(j)}-z+w)^+\wedge B^j$. Then $u(z-w,B)\in U$ and
--
--   $$
--   p_t\cdot u(z-w,B)+g_{t-1}\big(w,a_tu(z-w,B)\big)\ \le\ p_t\cdot u+g_{t-1}(w,a_tu)\qquad\text{for all } u\in U .
--   $$
--
--   Whatever amount of stock is issued in an interval, it is optimal to issue it to the classes in order of importance.
--
--   **Formalization Note.** Minimality is stated directly against every $u\in U$, not through the infimum defining $f_t(w;z,B)$.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 164–165, Lemma 4 with (4) and (5)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model
import Definitions.Def_TopkisRation_Levels_Split

namespace TopkisRation.Levels

theorem lemma_4 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ∈ Finset.Icc 1 M.k)
    (z : ℝ) (hz : 0 ≤ z) (B : Fin n → ℝ) (hB : 0 ≤ B)
    (w : ℝ) (hw : w ∈ Set.Icc (max (z - ∑ j, B j) 0) z) :
    uVec (z - w) B ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w} ∧
    ∀ u ∈ {u : Fin n → ℝ | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) = z - w},
      M.p t ⬝ᵥ uVec (z - w) B + M.g (t - 1) w (M.a t • uVec (z - w) B) ≤
        M.p t ⬝ᵥ u + M.g (t - 1) w (M.a t • u) := by sorry

end TopkisRation.Levels
