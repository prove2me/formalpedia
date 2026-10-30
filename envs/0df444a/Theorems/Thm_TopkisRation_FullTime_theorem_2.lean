-- Prove2me | Theorems.Thm_TopkisRation_FullTime_theorem_2
-- name    : TopkisRation.FullTime.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:40:39.01669+00:00
-- url     : https://prove2.me/theorems/6a50f476-d7a5-4386-98fe-aa9606eed65a
-- title:
--   Theorem 2 — critical rationing levels are monotone in time (full printed backlog scope)
-- statement:
--   Consider the $n$-class single-procurement model of §1 under assumptions (A)–(C). In interval $s$, nonnegative joint demand has finite coordinate means, demands in different intervals are independent, penalties satisfy $0\le p_s^1\le\cdots\le p_s^n$, and backlogs evolve as $b_{s-1}=a_su_s$ with arbitrary $a_s\ge0$. Holding and salvage costs satisfy the paper's convexity, continuity, and lower salvage-slope assumptions. Let $f_s,g_s$ be the optimal costs computed by (1).
--
--   For each class $j$, define
--
--   $$
--   \varphi_s^j(w)=p_s^j w+h_s(w)+g_{s-1}(w,a_sw\delta_j),\qquad w\ge0,
--   $$
--
--   where $\delta_j$ is its coordinate unit vector. Its critical level $\bar z_s^j$ is $+\infty$ if $\varphi_s^j$ is strictly decreasing on the whole half-line, and otherwise is its smallest minimizer there.
--
--   For every $1\le t<t+1\le k$ and every class $j$, if
--
--   $$
--   a_{t+1}=a_t=0,\qquad
--   p_{t+1}^j+\lim_{z\to\infty}D^+h_{t+1}(z)\le p_t^j,
--   $$
--
--   then
--
--   $$
--   \bar z_t^j\le\bar z_{t+1}^j.
--   $$
--
--   Every earlier backlog factor remains an arbitrary nonnegative real. The comparison includes equality in the slope hypothesis and zero or infinite critical levels. Since larger interval indices occur earlier in physical time, this says that the levels do not rise as those two intervals pass. It is a comparison of the defined critical levels; it does not assert global optimality of their rationing policy under fractional earlier backlogging.
--
--   **Formalization Note.** The model is the published TimeMono model. The limiting-slope bound is equivalently imposed at every nonnegative stock, including zero, using the canonical extended right derivative. The two WithTop real levels satisfy their exact least-minimizer or strictly-decreasing characterizations. Their existence follows from the model's convex continuous objectives, rather than an added hypothesis about arbitrary functions. The cost c is retained as model data but its procurement condition (D) is unused.
--
--   Differences from the source:
--   - generalization: Section 1 also imposes the procurement assumption (D) on c → No condition on the unused ordering cost c; reason: The rationing values and critical levels do not use c; (D) ensures procurement attainment only
--   - encoding: Classes 1 through n and valid backward interval indices → Classes Fin n with paper class j represented by j-1; natural interval indices with explicit bounds; reason: The same finite classes and intervals are represented; subtraction t-1 is used only for t at least 1
--   - encoding: Right derivatives on the nonnegative stock half-line → The canonical EReal right liminf of positive difference quotients, including stock zero; reason: For these convex continuous functions it is the right derivative, allowing minus infinity at the boundary
--   - reading: The first level-objective phrase on p. 166 omits w after p_t^j → The objective is p_t^j w+h_t(w)+g_{t-1}(w,a_t w delta_j); reason: The same sentence gives this complete objective in its smallest-minimum clause, as does the derivative argument
--   - encoding: The limiting holding slope in Theorem 2 → For every z at least zero, p_{t+1}^j plus the right slope of h_{t+1} at z is at most p_t^j in EReal; reason: Convexity makes the slopes nondecreasing, so the extended limit at infinity is their supremum; the two upper-bound conditions are equivalent
--   - encoding: The critical levels picked by their definition on p. 166 → Any two WithTop real values satisfying the canonical IsCriticalLevel predicates for the computed objectives; reason: Each convex continuous objective has a unique such level: its least nonnegative minimizer, or plus infinity if strictly decreasing; no additional regularity is assumed
-- source:
--   Topkis, Management Science 15(3) (1968), DOI 10.1287/mnsc.15.3.160, Theorem 2, p. 170 (PDF 12); §1 assumptions pp. 162–163 (PDF 4–5), (1) p. 163 (PDF 5), critical levels p. 166 (PDF 8)

import Mathlib
import Definitions.Def_TopkisRation_FullTime_ModelBridge

set_option autoImplicit false

namespace TopkisRation.FullTime

theorem theorem_2 {n : ℕ} (M : TopkisRation.TimeMono.Model n) (hM : M.Standing)
    (t : ℕ) (ht1 : 1 ≤ t) (htk : t + 1 ≤ M.k)
    (ha1 : M.a (t + 1) = 0) (ha0 : M.a t = 0) (j : Fin n)
    (hp : ∀ z : ℝ, 0 ≤ z →
      (M.p (t + 1) j : EReal) + TopkisRation.Levels.rightDeriv (M.h (t + 1)) z ≤
        (M.p t j : EReal))
    (z₀ z₁ : WithTop ℝ)
    (hz₀ : TopkisRation.Levels.IsCriticalLevel (M.levelObj t j) z₀)
    (hz₁ : TopkisRation.Levels.IsCriticalLevel (M.levelObj (t + 1) j) z₁) :
    z₀ ≤ z₁ := by sorry

end TopkisRation.FullTime
