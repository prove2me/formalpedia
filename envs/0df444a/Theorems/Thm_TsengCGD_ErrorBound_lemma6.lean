-- Prove2me | Theorems.Thm_TsengCGD_ErrorBound_lemma6
-- name    : TsengCGD.ErrorBound.lemma6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:02:28.497335+00:00
-- url     : https://prove2.me/theorems/e8d40cea-80bc-4222-9da8-e888766eb379
-- title:
--   Lemma 6 — ‖(d̃, δ̃)‖ ≤ κ‖d_I(x)‖ for P Lipschitz on dom P, κ depending only on the Lipschitz constant
-- statement:
--   Assume the standing assumptions of problem (1): $c > 0$, $P$ proper convex lower semicontinuous, $f$ continuously differentiable on an open set containing $\operatorname{dom}P$. Let $d_I(x)$ be the residual (13) and, for $\xi = P(x)$, let $(\tilde d,\tilde\delta)$ be an optimal solution of the subproblem
--   $$\min_{(d,\delta)} \Big\{ \nabla f(x)^\top d + \tfrac12\|d\|^2 + \tfrac12\delta^2 + c\delta \;\Big|\; (x+d,\ \xi+\delta) \in \operatorname{epi}P \Big\}. \qquad (42)$$
--
--   For every $K \ge 0$ there is a scalar $\kappa > 0$, depending only on $K$, such that whenever $P$ is Lipschitz continuous on $\operatorname{dom}P$ with constant $K$, then for every $x \in \operatorname{dom}P$
--   $$\big\|(\tilde d,\tilde\delta)\big\| \le \kappa\,\|d_I(x)\|.$$
--
--   The lemma compares the residual of the reformulation (41), a smooth problem over $\operatorname{epi}P$, with the residual $d_I$ of the original problem; it is what lets error bounds known for constrained smooth problems be transferred to (1).
--
--   **Formalization Note** $\kappa$ is quantified before the dimension $n$ and the data $f, P, c$, so it is a function of $K$ alone, as the paper says. The bound is asserted for every optimal solution of (42) (predicate `IsEpiSubSol`); the paper notes the solution is unique. $\|(d,\delta)\| = \sqrt{\|d\|^2 + \delta^2}$.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 410, Lemma 6 (with (42))

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions

namespace TsengCGD.ErrorBound

theorem lemma6 :
    ∀ K : ℝ, 0 ≤ K → ∃ κ > 0, ∀ {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ),
      TsengCGD.Global.Standing f D P c → PLipOn D P K →
        ∀ x ∈ D, ∀ (dt : TsengCGD.Global.Vec n) (δt : ℝ), IsEpiSubSol f D P c x (P x) dt δt →
          pairNorm dt δt ≤ κ * ‖TsengCGD.Global.dI f D P c x‖ := by sorry

end TsengCGD.ErrorBound
