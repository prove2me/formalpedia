-- Prove2me | Theorems.Thm_ProxAltMin_Conv_lemma_5_ii
-- name    : ProxAltMin.Conv.lemma_5_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:55.564974+00:00
-- url     : https://prove2.me/theorems/3365d1aa-4632-4406-9d18-17922d410e97
-- title:
--   Lemma 5 (ii) — the squared steps are summable, hence ‖xₖ − xₖ₋₁‖ + ‖yₖ − yₖ₋₁‖ → 0
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1), and let $(x_k,y_k)$ comply with the proximal alternating scheme (5)–(6). Then
--   $$\sum_{k=1}^{\infty}\big(\|x_k-x_{k-1}\|^2+\|y_k-y_{k-1}\|^2\big)<+\infty,$$
--   and hence $\lim_{k\to\infty}\big(\|x_k-x_{k-1}\|+\|y_k-y_{k-1}\|\big)=0$.
--
--   The vanishing of the steps is what lets limit points of the sequence be analysed through the optimality conditions of the scheme.
--
--   **Formalization Note** The series is written with the terms $\|x_{k+1}-x_k\|^2+\|y_{k+1}-y_k\|^2$, $k\ge0$, which is the same series re-indexed.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 6, Lemma 5 (ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Lemma 5 (ii) (p. 6): for every run of (5)–(6) under (H), (H1),
`∑_{k ≥ 1} (‖xₖ - x_{k-1}‖² + ‖yₖ - y_{k-1}‖²) < +∞`, hence `‖xₖ - x_{k-1}‖ + ‖yₖ - y_{k-1}‖ → 0`.
(The sum is written from `k = 0` with the terms `x_{k+1} - x_k`; it is the same series.) -/
theorem lemma_5_ii {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y) :
    Summable (fun k => ‖x (k + 1) - x k‖ ^ 2 + ‖y (k + 1) - y k‖ ^ 2) ∧
    Tendsto (fun k => ‖x (k + 1) - x k‖ + ‖y (k + 1) - y k‖) atTop (𝓝 0) := by sorry

end ProxAltMin.Conv
