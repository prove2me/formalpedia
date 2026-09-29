-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_schur_reformulation
-- name    : RobustSDP.Uniqueness.schur_reformulation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:06:31.593133+00:00
-- url     : https://prove2.me/theorems/40ed4945-dab6-4158-a0b8-28d2c11e50d6
-- title:
--   §4.2 — Schur complement: for τ > 0, (x, τ) is feasible for (15) iff G(x, τ) ⪰ 0
-- statement:
--   Let $x \in \mathbb{R}^m$ and $\tau > 0$. Then $(x,\tau)$ is feasible for the SDP (15) if and only if the matrix $G(x,\tau) = F(x) - \tau LL^T - \frac{1}{\tau}R(x)^TR(x)$ is positive semidefinite:
--   $$\begin{bmatrix} F(x) - \tau L L^T & R(x)^T \\ R(x) & \tau I \end{bmatrix} \succeq 0 \iff F(x) - \tau L L^T - \frac{1}{\tau} R(x)^T R(x) \succeq 0 .$$
--
--   Together with $\tau_{\mathrm{opt}} > 0$ this is how the paper rewrites (15) as the nonlinear program (16), $\min d^Ty$ subject to $G(y) \succeq 0$, with $d = (c, 0)$ and $y = (x, \tau)$.
--
--   **Formalization Note** The paper's (16) also carries the scalar constraint $\tau - 0.99\,\tau_{\mathrm{opt}} \ge 0$ (the second block of $\mathcal{G}(y) = \mathrm{diag}(G(y), \tau - .99\tau_{\mathrm{opt}})$), which only keeps $\tau$ away from $0$; the statement here is the Schur complement equivalence on which the rewriting rests, stated for every $\tau > 0$.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 39, §4.2, definition of G(y) and Eq. (16)

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- §4.2, p. 39 (Schur complement step behind (16)): for `τ > 0`, `(x, τ)` is feasible for (15)
iff `G(x, τ) = F(x) − τLLᵀ − (1/τ)R(x)ᵀR(x) ⪰ 0`. -/
theorem schur_reformulation {m n p q : ℕ} (D : SDPData m n p q) (x : Fin m → ℝ) (τ : ℝ)
    (hτ : 0 < τ) :
    D.Feasible (x, τ) ↔ (D.G (x, τ)).PosSemidef := by sorry

end RobustSDP.Uniqueness
