-- Prove2me | Theorems.Thm_TopkisRation_Levels_lemma_3
-- name    : TopkisRation.Levels.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:49:18.644031+00:00
-- url     : https://prove2.me/theorems/ef716651-45eb-4891-8f71-fdd7c849fd57
-- title:
--   Lemma 3, p. 164 — moving ε of demand from class i to a less important class j does not raise f_t or g_t
-- statement:
--   In the model of Topkis (1968, §1) under Assumptions (A)–(C), let $i>j$ be two demand classes, $\delta_i,\delta_j$ the corresponding unit vectors, and $\varepsilon>0$. Then:
--   1. for $1\le t\le k$, $z\ge0$ and $B\ge0$ with $B^i\ge\varepsilon$,
--   $$
--   f_t(z,B)\ \ge\ f_t\big(z,\,B-\varepsilon(\delta_i-\delta_j)\big); \tag{2}
--   $$
--   2. for $0\le t\le k$, $z\ge0$ and $b\ge0$ with $b^i\ge\varepsilon$,
--   $$
--   g_t(z,b)\ \ge\ g_t\big(z,\,b-\varepsilon(\delta_i-\delta_j)\big). \tag{3}
--   $$
--
--   Demand of a more important class is never cheaper to face than the same amount of a less important class. The lemma relies on the backlog relation $b_{t-1}=a_tu_t$, and it is used to show that the priority vector (5) is optimal (Lemma 4).
--
--   **Formalization Note.** The page states the single hypothesis $b^i\wedge B^i\ge\varepsilon>0$ for both displays; each display carries here the part that concerns its own vector, which is the same claim.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 164, Lemma 3, (2) and (3)

import Mathlib
import Definitions.Def_TopkisRation_Levels_Model

namespace TopkisRation.Levels

theorem lemma_3 {n : ℕ} (M : Model n) (hM : M.Standing) (i j : Fin n) (hij : j < i)
    (ε : ℝ) (hε : 0 < ε) :
    (∀ t ∈ Finset.Icc 1 M.k, ∀ z, 0 ≤ z → ∀ B : Fin n → ℝ, 0 ≤ B → ε ≤ B i →
      M.f t z (B - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.f t z B) ∧
    (∀ t ≤ M.k, ∀ z, 0 ≤ z → ∀ b : Fin n → ℝ, 0 ≤ b → ε ≤ b i →
      M.g t z (b - ε • (Pi.single i 1 - Pi.single j 1)) ≤ M.g t z b) := by sorry

end TopkisRation.Levels
