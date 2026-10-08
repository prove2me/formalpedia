-- Prove2me | Theorems.Thm_ProxLoj_Conv_prop_2_i_ii
-- name    : ProxLoj.Conv.prop_2_i_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:37:27.87423+00:00
-- url     : https://prove2.me/theorems/40fb2b4e-f8eb-4cf8-8df6-f42c9b56b95d
-- title:
--   Proposition 2 (i)–(ii), p. 3 — along a proximal run f(x^k) is nonincreasing and Σ|x^{k+1} − x^k|² < +∞
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be proper with $\inf f>-\infty$ (H1), let $0<\lambda_-<\lambda_+$ and $\lambda_k\in(\lambda_-,\lambda_+)$ for all $k$, and let $(x^k)$ comply with (2). Then
--
--   1. the sequence $(f(x^k))_{k\in\mathbb N}$ is nonincreasing, and
--   2. $$\sum_{k=0}^{\infty}|x^{k+1}-x^k|^2<+\infty.$$
--
--   These are the basic descent facts of the proximal algorithm; (ii) gives $|x^{k+1}-x^k|\to0$, on which every later statement rests.
--
--   **Formalization Note** The page's "decreasing" is read as nonincreasing (the proof's own word); repeated points $x^{k+1}=x^k$ are allowed. $f(x^0)$ may be $+\infty$; the statement does not assume $f(x^0)<+\infty$. Lower semicontinuity and (H2)–(H3) are not needed and are dropped.
-- source:
--   Attouch & Bolte, On the convergence of the proximal algorithm for nonsmooth functions involving analytic features, author's version hal-00803898v1, p. 3, Proposition 2 (i)–(ii); proof sketch p. 4, (4)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope
import Definitions.Def_ProxLoj_Conv_Setting

open Filter Topology NonconvexSplitting.Shared NonsmoothLojasiewicz.Continuous

namespace ProxLoj.Conv

/-- Proposition 2 (i)–(ii), p. 3: along a proximal run, `f(x^k)` is nonincreasing and
`Σ_k ‖x^{k+1} - x^k‖² < +∞`. -/
theorem prop_2_i_ii {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hproper : IsProper f)
    (hH1 : H1 f) (lam : ℕ → ℝ) (lamMinus lamPlus : ℝ) (hstep : StepBounds lam lamMinus lamPlus)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : IsProxRun f lam x) :
    Antitone (fun k => f (x k)) ∧ Summable (fun k => ‖x (k + 1) - x k‖ ^ 2) := by sorry

end ProxLoj.Conv
