-- Prove2me | Theorems.Thm_TopkisRation_TimeMono_lemma_7
-- name    : TopkisRation.TimeMono.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:54.771363+00:00
-- url     : https://prove2.me/theorems/9bd6dae2-d3e3-41e9-85e9-a97f176fda33
-- title:
--   Lemma 7, p. 169 — if a_t = 1 or b = 0: D⁺h_t(z) + D_z⁺g_{t−1}(z, b) ≥ D_z⁺g_t(z, b)
-- statement:
--   Consider the $n$-class rationing model with the standing assumptions (A)–(C) and the expected optimal costs $g_t$, $g_{t-1}$. Let $1 \le t \le k$ and suppose that $a_i \in \{0,1\}$ for every $1 \le i \le t$. Let $z \ge 0$ and $b \ge 0$, and suppose that either $a_t = 1$ or $b = 0$. Then
--   $$
--   D_z^+ g_t(z,b) \le D^+h_t(z) + D_z^+ g_{t-1}(z,b).
--   $$
--
--   Ignoring the holding cost in interval $t$, at a given stock and backlog level the marginal value of additional stock is no less in interval $t$ than in interval $t-1$. The paper notes that the claim can fail when $a_t = 0$ and $b \ne 0$. With $b = 0$ it is the step that yields Theorem 2.
--
--   **Formalization Note.** Right derivatives and their sum are taken in the extended reals; $-\infty + x = -\infty$ is the paper's convention. No term is $+\infty$, since a convex function on $[0,\infty)$ has a finite right difference quotient at every point. The hypothesis "$a_i$ is 0 or 1 for each $i$" is required for $1 \le i \le t$, the intervals $g_t$ depends on.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 169, Lemma 7

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model

namespace TopkisRation.TimeMono

theorem lemma_7 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htk : t ≤ M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (z : ℝ) (hz : 0 ≤ z) (b : Fin n → ℝ) (hb : 0 ≤ b) (hcase : M.a t = 1 ∨ b = 0) :
    TopkisRation.Levels.rightDeriv (fun z => M.g t z b) z ≤
      TopkisRation.Levels.rightDeriv (M.h t) z + TopkisRation.Levels.rightDeriv (fun z => M.g (t - 1) z b) z := by sorry

end TopkisRation.TimeMono
