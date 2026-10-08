-- Prove2me | Theorems.Thm_TsengCGD_ErrorBound_lemma7
-- name    : TsengCGD.ErrorBound.lemma7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:02:00.446198+00:00
-- url     : https://prove2.me/theorems/3d04111f-33b2-4747-9928-dfd63fe9414b
-- title:
--   Lemma 7 — under C1, C2 or C3 and X̄ ≠ ∅, dist(x, X̄) ≤ τ′‖(d̃, δ̃)‖ locally (44)
-- statement:
--   Assume the standing assumptions of problem (1), that the set $\bar X$ of stationary points of $F_c = f + cP$ is nonempty, and that one of the following holds:
--   1. **C1**: $f$ is quadratic and $P$ is polyhedral;
--   2. **C2**: $f(x) = g(Ex) + q^\top x$ for all $x$, with $E \in \mathbb R^{m\times n}$, $q \in \mathbb R^n$, $g$ strongly convex and differentiable on $\mathbb R^m$ with $\nabla g$ Lipschitz on $\mathbb R^m$, and $P$ polyhedral;
--   3. **C3**: $f(x) = \max_{y\in Y}\{(Ex)^\top y - g(y)\} + q^\top x$ for all $x$, with $Y \subseteq \mathbb R^m$ polyhedral, $E, q, g$ as in C2, and $P$ polyhedral.
--
--   Then for every $\zeta \in \mathbb R$ there are scalars $\tau' > 0$ and $\epsilon' > 0$ such that, for every $x \in \operatorname{dom}P$,
--   $$\operatorname{dist}(x,\bar X) \le \tau'\,\big\|(\tilde d,\tilde\delta)\big\| \quad\text{whenever } F_c(x) \le \zeta,\ \big\|(\tilde d,\tilde\delta)\big\| \le \epsilon', \qquad (44)$$
--   where $(\tilde d,\tilde\delta)$ is the optimal solution of the subproblem (42) with $\xi = P(x)$.
--
--   This is a local error bound for the reformulation (41) of problem (1) as a smooth problem over the polyhedral set $\operatorname{epi}P$, stated in terms of its projection residual; combined with Lemma 6 it gives Assumption 2(a).
--
--   **Formalization Note** $\tau'$ and $\epsilon'$ are chosen after $\zeta$ and before $x$. "$F_c(x) \le \zeta$" carries $x \in \operatorname{dom}P$ explicitly. The bound is asserted for every optimal solution of (42) (predicate `IsEpiSubSol`). $\operatorname{dist}$ is the infimum distance `Metric.infDist`. The conditions C1–C3 are those of the definition file `TsengCGD.ErrorBound.Conditions`.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 411, Lemma 7, (44)

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions

namespace TsengCGD.ErrorBound

theorem lemma7 {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c) (hX : (TsengCGD.Linear.statSet f D P c).Nonempty)
    (hC : C1 f D P ∨ C2 f D P ∨ C3 f D P) :
    ∀ ζ : ℝ, ∃ τ' > 0, ∃ ε' > 0, ∀ x ∈ D, TsengCGD.Global.Fc f P c x ≤ ζ →
      ∀ (dt : TsengCGD.Global.Vec n) (δt : ℝ), IsEpiSubSol f D P c x (P x) dt δt → pairNorm dt δt ≤ ε' →
        Metric.infDist x (TsengCGD.Linear.statSet f D P c) ≤ τ' * pairNorm dt δt := by sorry

end TsengCGD.ErrorBound
