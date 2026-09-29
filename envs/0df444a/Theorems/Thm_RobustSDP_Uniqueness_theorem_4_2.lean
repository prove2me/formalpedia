-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_theorem_4_2
-- name    : RobustSDP.Uniqueness.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:08:34.314854+00:00
-- url     : https://prove2.me/theorems/1eb153b4-4bd7-4bd7-bebd-33c9fa638a4f
-- title:
--   Theorem 4.2 — Under H1–H3 the SDP (15) has quadratic growth at every optimum and a unique solution
-- statement:
--   Consider the semidefinite program in the variables $(x,\tau) \in \mathbb{R}^m \times \mathbb{R}$,
--   $$\text{minimize } c^T x \quad\text{subject to}\quad \begin{bmatrix} F(x) - \tau L L^T & R(x)^T \\ R(x) & \tau I \end{bmatrix} \succeq 0, \tag{15}$$
--   where $F(x) = F_0 + \sum_i x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$, $R(x) = R_0 + \sum_i x_i R_i$ with $R_i \in \mathbb{R}^{q\times n}$, $L \in \mathbb{R}^{n\times p}$, and $c \in \mathbb{R}^m \setminus \{0\}$. This is the robust counterpart of an uncertain SDP under full norm-bounded perturbations with $D = 0$ and $\rho = 1$.
--
--   Assume
--
--   1. **H1**: (15) is strictly feasible;
--   2. **H2**: (15) is inf-compact: every sublevel set $\{(x,\tau) \text{ feasible} : c^Tx \le M\}$ is bounded;
--   3. **H3(a)**: the nullspace of $\lambda R_0 + \sum_i x_i R_i$ is the same proper subspace of $\mathbb{R}^n$ for all $(\lambda, x) \ne (0,0)$;
--   4. **H3(b)**: $\begin{bmatrix} L^T \\ R(x)\end{bmatrix}$ has full column rank for every $x$.
--
--   Then (15) satisfies the quadratic growth condition at every optimal point $y_{\mathrm{opt}} = (x_{\mathrm{opt}}, \tau_{\mathrm{opt}})$: there are $\alpha, \varepsilon > 0$ such that every feasible $y = (x, \tau)$ with $\|y - y_{\mathrm{opt}}\| < \varepsilon$ satisfies
--   $$c^T x \ \ge\ c^T x_{\mathrm{opt}} + \alpha \|y - y_{\mathrm{opt}}\|^2 .$$
--   Consequently (15) has exactly one optimal point $(x, \tau)$.
--
--   Uniqueness of the robust solution is what makes robustification a regularization of ill-posed SDPs, and quadratic growth is the property from which the paper's Hölder-stability results follow.
--
--   **Formalization Note** The conclusion has both parts of the theorem: quadratic growth at every optimal point, and existence and uniqueness of the optimal pair $(x,\tau)$ (existence is part of the paper's claim, via H1 and H2). $\|\cdot\|$ is the Euclidean norm on $\mathbb{R}^{m+1}$; the paper's $o(\|y - y_{\mathrm{opt}}\|^2)$ form of the QGC is equivalent to this local form. The QGC is stated for (15) rather than for the paper's reformulation (16), with which it agrees near $y_{\mathrm{opt}}$ because $\tau_{\mathrm{opt}} > 0$. The standing assumptions $c \neq 0$ (p. 33) and symmetry of $F_0, \dots, F_m$ (p. 33) are explicit hypotheses.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 39, Theorem 4.2 (with Eq. (15) and Hypotheses H1–H3, p. 38; proof in Appendix A, pp. 48–50)

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- **Theorem 4.2** (El Ghaoui–Oustry–Lebret 1998, p. 39). If H1–H3 hold, the SDP (15) satisfies the
quadratic growth condition at every optimal point `y_opt = (x_opt, τ_opt)`; consequently (15) has
a unique solution `(x, τ)`. Standing assumptions: `c ≠ 0` and `F₀, …, F_m` symmetric (p. 33). -/
theorem theorem_4_2 {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c) (h3a : D.H3a) (h3b : D.H3b) :
    (∀ y : (Fin m → ℝ) × ℝ, D.IsOptimal c y → D.QGC c y) ∧
      ∃! y : (Fin m → ℝ) × ℝ, D.IsOptimal c y := by sorry

end RobustSDP.Uniqueness
