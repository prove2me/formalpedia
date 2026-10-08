-- Prove2me | Theorems.Thm_TopkisRation_TimeMono_lemma_5
-- name    : TopkisRation.TimeMono.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:47:41.109467+00:00
-- url     : https://prove2.me/theorems/21d7c524-233f-450b-a986-f50a4133936c
-- title:
--   Lemma 5, p. 168 — the marginal value of stock is nondecreasing in the backlog vector: D_z⁺g_t(z, b) ≥ D_z⁺g_t(z, b̄) for b ≤ b̄
-- statement:
--   Consider the $n$-class rationing model with the standing assumptions (A)–(C), and let $g_t(z,b)$ be the expected optimal cost of the last $t$ intervals given stock $z$ and backlog vector $b$ at the start of interval $t$. Suppose that $a_i \in \{0,1\}$ for every interval $1 \le i \le t$, where $0 \le t \le k$. Then for every stock level $z \ge 0$ and backlog vectors $0 \le b \le \bar b$ (componentwise),
--   $$
--   D_z^+ g_t(z,\bar b) \le D_z^+ g_t(z,b),
--   $$
--   where $D_z^+$ is the right derivative in $z$.
--
--   Since $-D_z^+g_t$ is the marginal value of an extra unit of stock, this says that at any stock level the marginal value of stock is a nondecreasing function of the backlogs. It is one of the two monotonicity facts behind Lemma 7.
--
--   **Formalization Note.** The paper writes "suppose $a_t$ is 0 or 1 for each $t$"; since $g_t$ depends only on $a_1,\dots,a_t$, the hypothesis is required only for $1 \le i \le t$, which makes the statement (formally) stronger. Right derivatives take values in the extended reals.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 168, Lemma 5

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model

namespace TopkisRation.TimeMono

theorem lemma_5 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht : t ≤ M.k)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1)
    (z : ℝ) (hz : 0 ≤ z) (b bbar : Fin n → ℝ) (hb : 0 ≤ b) (hbb : b ≤ bbar) :
    TopkisRation.Levels.rightDeriv (fun z => M.g t z bbar) z ≤ TopkisRation.Levels.rightDeriv (fun z => M.g t z b) z := by sorry

end TopkisRation.TimeMono
