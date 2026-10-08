-- Prove2me | Theorems.Thm_ProxAltMin_Conv_lemma_5_i
-- name    : ProxAltMin.Conv.lemma_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:39.125506+00:00
-- url     : https://prove2.me/theorems/cad73489-9d78-4623-9508-61c220a7b4eb
-- title:
--   Lemma 5 (i) — the sufficient decrease estimate (7); L(xₖ, yₖ) does not increase
-- statement:
--   Let $L=f+Q+g$ satisfy (H) and (H1) (relative to $y_0$, step sizes $\lambda_k,\mu_k\in(r_-,r_+)$), and let $(x_k,y_k)$ comply with the proximal alternating scheme (5)–(6). Then for every $k\ge1$
--   $$L(x_k,y_k)+\frac1{2\lambda_{k-1}}\|x_k-x_{k-1}\|^2+\frac1{2\mu_{k-1}}\|y_k-y_{k-1}\|^2\le L(x_{k-1},y_{k-1}),\tag{7}$$
--   and hence the sequence $L(x_k,y_k)$ does not increase.
--
--   The estimate (7) is the sufficient-decrease property on which all later convergence arguments rest.
--
--   **Formalization Note** (7) is an inequality in $\mathbb R\cup\{+\infty\}$; at $k=1$ the right-hand side may be $+\infty$.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 6, Lemma 5 (i), (7)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Lemma 5 (i) (p. 6), estimate (7): for every run of (5)–(6) under (H), (H1),
`L(xₖ, yₖ) + ‖xₖ - x_{k-1}‖² / (2λ_{k-1}) + ‖yₖ - y_{k-1}‖² / (2μ_{k-1}) ≤ L(x_{k-1}, y_{k-1})` for all
`k ≥ 1` (in `ℝ ∪ {+∞}`); hence `L(xₖ, yₖ)` does not increase. -/
theorem lemma_5_i {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu (y 0) rm rp)
    (hrun : IsPAMRun f Q g lam mu x y) :
    (∀ k : ℕ, 1 ≤ k →
      L f Q g (pt (x k) (y k)) + ((‖x k - x (k - 1)‖ ^ 2 / (2 * lam (k - 1)) : ℝ) : EReal) +
          ((‖y k - y (k - 1)‖ ^ 2 / (2 * mu (k - 1)) : ℝ) : EReal) ≤
        L f Q g (pt (x (k - 1)) (y (k - 1)))) ∧
    Antitone (fun k => L f Q g (pt (x k) (y k))) := by sorry

end ProxAltMin.Conv
