-- Prove2me | Theorems.Thm_ProxAltMin_Conv_lemma_5_exists
-- name    : ProxAltMin.Conv.lemma_5_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:08:44.382133+00:00
-- url     : https://prove2.me/theorems/4ebc9ebb-17f3-4e35-b3b4-ff7685f1bfd0
-- title:
--   Lemma 5 — under (H), (H1) the proximal alternating sequences are correctly defined from every initial point
-- statement:
--   Let $L(x,y)=f(x)+Q(x,y)+g(y)$ satisfy (H), let $(x_0,y_0)\in\mathbb R^n\times\mathbb R^m$, and let the step sizes $(\lambda_k)$, $(\mu_k)$ satisfy (H1) relative to $y_0$: $\inf L>-\infty$, $L(\cdot,y_0)$ is proper, and $\lambda_k,\mu_k\in(r_-,r_+)$ with $0<r_-<r_+$.
--
--   Then sequences $(x_k)_{k\ge0}$, $(y_k)_{k\ge0}$ starting at $(x_0,y_0)$ and complying with (5)–(6) exist:
--   $$x_{k+1}\in\operatorname{argmin}_u\Big\{L(u,y_k)+\tfrac1{2\lambda_k}\|u-x_k\|^2\Big\},\qquad y_{k+1}\in\operatorname{argmin}_v\Big\{L(x_{k+1},v)+\tfrac1{2\mu_k}\|v-y_k\|^2\Big\}\quad(k\ge0).$$
--
--   This is the first sentence of Lemma 5: every minimization problem of the scheme has a solution, so the scheme can be run. It shows that the hypotheses of the convergence theorems are satisfiable.
-- source:
--   Attouch, Bolte, Redont, Soubeyran, Proximal alternating minimization and projection methods for nonconvex problems, Math. Oper. Res. (2010), p. 6, Lemma 5 (first sentence)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_ProxAltMin_Conv_Setting
open NonconvexSplitting.Shared
open Filter Topology

namespace ProxAltMin.Conv

/-- Lemma 5, first sentence (p. 6): under (H) and (H1), for every initial point `(x₀, y₀)` the
proximal alternating scheme (5)–(6) can be run, i.e. sequences complying with (5)–(6) and starting at
`(x₀, y₀)` exist. -/
theorem lemma_5_exists {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (Q : Z n m → ℝ)
    (g : EuclideanSpace ℝ (Fin m) → EReal) (lam mu : ℕ → ℝ) (rm rp : ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (y0 : EuclideanSpace ℝ (Fin m))
    (hH : AssumptionH f Q g) (hH1 : AssumptionH1 f Q g lam mu y0 rm rp) :
    ∃ (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin m)),
      x 0 = x0 ∧ y 0 = y0 ∧ IsPAMRun f Q g lam mu x y := by sorry

end ProxAltMin.Conv
