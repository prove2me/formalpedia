-- Prove2me | Theorems.Thm_TsengCGD_ErrorBound_theorem4
-- name    : TsengCGD.ErrorBound.theorem4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:04:35.716992+00:00
-- url     : https://prove2.me/theorems/84200715-e401-46ee-aaad-69dbfbf24a7a
-- title:
--   Theorem 4 — Assumption 2(a) holds if X̄ ≠ ∅ and C1, C2 or C3 holds, or if f is strongly convex with Lipschitz gradient (C4)
-- statement:
--   Assume the standing assumptions of problem (1): $c > 0$, $P:\mathbb R^n\to(-\infty,\infty]$ proper, convex and lower semicontinuous, $f$ continuously differentiable on an open set containing $\operatorname{dom}P$, and $F_c = f + cP$. Let $\bar X$ be the set of stationary points of $F_c$ and $d_I(x)$ the residual (13).
--
--   Suppose that either
--   1. $\bar X \neq \emptyset$ and one of the conditions C1, C2, C3 of Lemma 7 holds ($P$ polyhedral, and $f$ quadratic, or $f(x) = g(Ex) + q^\top x$, or $f(x) = \max_{y\in Y}\{(Ex)^\top y - g(y)\} + q^\top x$ with $g$ strongly convex with Lipschitz gradient and $Y$ polyhedral); or
--   2. **C4**: $f$ is strongly convex and satisfies (22), $\|\nabla f(y) - \nabla f(z)\| \le L\|y - z\|$ on $\operatorname{dom}P$, for some $L \ge 0$.
--
--   Then Assumption 2(a) holds: $\bar X \neq \emptyset$ and for every $\zeta$ there are $\tau > 0$ and $\epsilon > 0$ such that
--   $$\operatorname{dist}(x,\bar X) \le \tau\,\|d_I(x)\| \quad\text{whenever } x \in \operatorname{dom}P,\ F_c(x) \le \zeta,\ \|d_I(x)\| \le \epsilon.$$
--
--   This is the main result of §6 of the paper: it identifies problem classes for which the linear convergence theorem of the coordinate gradient descent method applies, among them $\ell_1$-regularized least squares and other problems with polyhedral $P$ and quadratic or composite $f$.
--
--   **Formalization Note** Under C4 the conclusion includes $\bar X \neq \emptyset$, which is not assumed (the paper's proof notes that $\bar X$ is then a singleton). In C4 strong convexity and (22) are required on $\operatorname{dom}P$ only, which is weaker than the paper's "strongly convex" on $\mathbb R^n$, so the statement is at least as strong as printed. Assumption 2(a) quantifies over every real $\zeta$; the paper's "$\zeta \ge \min_x F_c(x)$" agrees with this since the condition is vacuous below $\inf F_c$. $\operatorname{dist}$ is `Metric.infDist`.
-- source:
--   Tseng and Yun, A coordinate gradient descent method for nonsmooth separable minimization, Math. Program. Ser. B 117 (2009), p. 412, Theorem 4 (Assumption 2(a), p. 404)

import Mathlib
import Definitions.Def_TsengCGD_Linear_Basic
import Definitions.Def_TsengCGD_ErrorBound_Conditions

namespace TsengCGD.ErrorBound

theorem theorem4 {n : ℕ} (f : TsengCGD.Global.Vec n → ℝ) (D : Set (TsengCGD.Global.Vec n)) (P : TsengCGD.Global.Vec n → ℝ) (c : ℝ)
    (hs : TsengCGD.Global.Standing f D P c)
    (hC : ((TsengCGD.Linear.statSet f D P c).Nonempty ∧ (C1 f D P ∨ C2 f D P ∨ C3 f D P)) ∨ C4 f D) :
    TsengCGD.Linear.Assumption2a f D P c := by sorry

end TsengCGD.ErrorBound
