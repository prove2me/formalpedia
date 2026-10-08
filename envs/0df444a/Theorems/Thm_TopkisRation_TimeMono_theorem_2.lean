-- Prove2me | Theorems.Thm_TopkisRation_TimeMono_theorem_2
-- name    : TopkisRation.TimeMono.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:21.097233+00:00
-- url     : https://prove2.me/theorems/5461c81c-6475-4ed6-a984-652bc5a764e9
-- title:
--   Theorem 2, p. 170 — if a_{t+1} = a_t = 0 and p_{t+1}^j + lim D⁺h_{t+1} ≤ p_t^j, then z̄_t^j ≤ z̄_{t+1}^j
-- statement:
--   Consider the $n$-class rationing model with the standing assumptions (A)–(C). For an interval $t$ and a class $j$, the **critical rationing level** $\bar z_t^j \in [0,\infty]$ is $+\infty$ if
--   $$
--   \varphi_t^j(w) = p_t^j w + h_t(w) + g_{t-1}(w, a_t w \delta_j)
--   $$
--   is strictly decreasing on $[0,\infty)$, and is the smallest minimizer of $\varphi_t^j$ on $[0,\infty)$ otherwise; class $j$ demand is served from stock only while the stock stays at or above $\bar z_t^j$.
--
--   Let $1 \le t$ and $t+1 \le k$, so that intervals $t+1$ and $t$ are consecutive (interval $t+1$ comes first, since intervals are indexed by the number remaining). Suppose there is no backlogging in either interval, $a_{t+1} = a_t = 0$, that $a_i \in \{0,1\}$ for $1 \le i \le t$, and that for class $j$
--   $$
--   p_{t+1}^j + \lim_{z\to\infty} D^+h_{t+1}(z) \le p_t^j .
--   $$
--   Then
--   $$
--   \bar z_t^j \le \bar z_{t+1}^j .
--   $$
--
--   So without backlogging, and when the class-$j$ penalty does not grow too fast toward the end of the period relative to the marginal holding cost, the critical rationing levels are nondecreasing in $t$: one rations class $j$ at least as strictly in earlier intervals as in later ones. The paper shows by an example that the analogous result fails in the backlog case.
--
--   **Formalization Note.**
--   1. The critical levels are taken as any values in $[0,\infty]$ (`WithTop ℝ`) satisfying the defining property, as the paper "picks" them.
--   2. Since $h_{t+1}$ is convex, $D^+h_{t+1}$ is nondecreasing on $[0,\infty)$, so its limit is $\le c$ exactly when every value is; the hypothesis is stated as $p_{t+1}^j + D^+h_{t+1}(z) \le p_t^j$ for all $z \ge 0$, in the extended reals.
--   3. **Disclosed addition.** The theorem as printed names only $a_{t+1} = a_t = 0$. Its proof applies Lemma 7 at interval $t$, which assumes that $a_i$ is 0 or 1 for each $i$; the Lean statement therefore assumes $a_i \in \{0,1\}$ for $1 \le i \le t-1$ as well (for $i = t$ it is implied). Whether the theorem holds without it is not shown in the paper.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), p. 170, Theorem 2

import Mathlib
import Definitions.Def_TopkisRation_TimeMono_Model

namespace TopkisRation.TimeMono

theorem theorem_2 {n : ℕ} (M : Model n) (hM : M.Standing) (t : ℕ) (ht1 : 1 ≤ t)
    (htk : t + 1 ≤ M.k) (ha1 : M.a (t + 1) = 0) (ha0 : M.a t = 0)
    (ha : ∀ i ∈ Finset.Icc 1 t, M.a i = 0 ∨ M.a i = 1) (j : Fin n)
    (hp : ∀ z : ℝ, 0 ≤ z →
      (M.p (t + 1) j : EReal) + TopkisRation.Levels.rightDeriv (M.h (t + 1)) z ≤ (M.p t j : EReal))
    (z₀ z₁ : WithTop ℝ) (hz₀ : TopkisRation.Levels.IsCriticalLevel (M.levelObj t j) z₀)
    (hz₁ : TopkisRation.Levels.IsCriticalLevel (M.levelObj (t + 1) j) z₁) :
    z₀ ≤ z₁ := by sorry

end TopkisRation.TimeMono
