-- Prove2me | Theorems.Thm_RobustSDP_FullPert_Supplement_theorem_4_1
-- name    : RobustSDP.FullPert.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:46:00.44348+00:00
-- url     : https://prove2.me/theorems/6d946094-440c-4bc0-b2c7-35cd80f3f9d2
-- title:
--   Theorem 4.1, corrected — quadratic growth from a complementary stationary multiplier and positive Hessian
-- statement:
--   Consider the robust SDP (15) of El Ghaoui, Oustry and Lebret under full perturbations with $D = 0$ and $\rho = 1$:
--   $$\text{minimize } c^T x \ \text{ subject to } \ \begin{bmatrix} F(x) - \tau LL^T & R(x)^T \\ R(x) & \tau I \end{bmatrix} \succeq 0,$$
--   where $F(x) = F_0 + \sum_i x_i F_i$ with symmetric $F_i \in \mathbb{R}^{n\times n}$, $R(x) = R_0 + \sum_i x_i R_i \in \mathbb{R}^{q\times n}$, $L \in \mathbb{R}^{n\times p}$, and $c \in \mathbb{R}^m$, $c \ne 0$. Let $y_{\mathrm{opt}} = (x_{\mathrm{opt}}, \tau_{\mathrm{opt}})$ be optimal for (15) with $\tau_{\mathrm{opt}} > 0$. Use the corrected KKT multiplier set, with $\operatorname{Tr}(Y\mathcal G(y_{\mathrm{opt}}))=0$, and the notation of §4.2–§4.3: $G$, $\mathcal{G}$, problem (16), the Lagrangian $\mathcal{L}$ and the dual set $\mathcal{Y}(y_{\mathrm{opt}})$.
--
--   Assume:
--   1. **H1** (Slater): the constraint matrix of (15) is positive definite at some $(x, \tau)$;
--   2. **H2** (inf-compactness): every set $\{(x,\tau) \text{ feasible for (15)} : c^T x \le M\}$ is bounded;
--   3. condition (17): there is $Y \in \mathcal{Y}(y_{\mathrm{opt}})$ such that
--   $$\nabla^2_{yy}\, \mathcal{L}(y_{\mathrm{opt}}, Y) \succ 0 .$$
--
--   Then problem (16) satisfies the quadratic growth condition at $y_{\mathrm{opt}}$: there are $\alpha > 0$ and $\varepsilon > 0$ such that every $y$ feasible for (16) with $\|y - y_{\mathrm{opt}}\| < \varepsilon$ satisfies
--   $$c^T x \ \ge\ c^T x_{\mathrm{opt}} + \alpha\, \|y - y_{\mathrm{opt}}\|^2 .$$
--
--   The theorem replaces hypothesis H3 of Theorem 4.2 by the second-order condition (17) at a single optimal point. Quadratic growth is the property from which the paper's uniqueness and regularity results are derived.
--
--   **Formalization Note** The data of (15) are `RobustSDP.Uniqueness.SDPData`. H1, H2, symmetry of the $F_i$ and optimality are the published predicates `Slater`, `InfCompact`, `Symmetric` and `IsOptimal`. The Hessian condition says that the second Fréchet derivative of $y \mapsto \mathcal{L}(y, Y)$ at $y_{\mathrm{opt}}$ is positive in every nonzero direction (`iteratedFDeriv ℝ 2 … ![h, h] > 0`), the convention of the published Appendix A item.
--
--
--   **Source correction.** The printed theorem is false with its displayed stationarity-only dual set. This item requires complementary slackness, as used in Appendix A. It excludes the noncomplementary stationary certificates in DISPROOF.md.
--
--   Differences from the source:
--   - correction: the displayed set 𝒴 contains PSD stationary matrices without complementary slackness → dualSet also requires Tr(Y𝒢(y_opt)) = 0; reason: the stationarity-only version is false on the explicit 2-by-2 example in DISPROOF.md; Appendix A invokes complementarity; all KKT multipliers are retained.
--   - reading: "with the notation above", i.e. an optimal (x_opt, τ_opt) of (15) with τ_opt > 0, which §4.2 derives from H3(a) → y_opt optimal for (15) and τ_opt > 0 are hypotheses; reason: Theorem 4.1 does not assume H3, and the notation of §4.2 (1/τ, the cut-off 0.99 τ_opt, problem (16)) is only defined when τ_opt > 0.
--   - encoding: Tr Y ∂𝒢/∂yᵢ(y_opt) = dᵢ → partial derivative at y_opt of y ↦ Tr Y𝒢(y) in the i-th coordinate equals dᵢ; reason: trace and multiplication by Y are linear and 𝒢 is differentiable near y_opt because τ_opt > 0, so the two quantities are equal.
--   - encoding: QGC with a remainder o(‖y − y_opt‖²) for every feasible y → local bound with α > 0 on a Euclidean ball of radius ε > 0; reason: the two forms are equivalent (halve α; conversely take a zero remainder near y_opt).
--   - encoding: feasibility for (16) is 𝒢(y) ⪰ 0 on the domain τ > 0 → τ > 0 is written into feasibility; reason: it is the domain of the notation of §4.2 and follows from τ ≥ 0.99 τ_opt > 0.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 39, Theorem 4.1 and Eq. (17); §4.2–§4.3, p. 39; §4 and §4.1 (H1, H2), p. 38

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses
import Definitions.Def_RobustSDP_FullPert_Supplement_NonlinearProgram

open Matrix

namespace RobustSDP.FullPert.Supplement

open RobustSDP.Uniqueness

/-- **Theorem 4.1, corrected** (El Ghaoui–Oustry–Lebret 1998, p. 39). Full perturbations, `D = 0`, `ρ = 1`
(§4, p. 38). Let `y_opt = (x_opt, τ_opt)` be optimal for the SDP (15), with `τ_opt > 0` (the
notation of §4.2). If H1 (Slater) and H2 (inf-compactness) hold, and some
`Y ∈ 𝒴(y_opt)` satisfying complementary slackness makes the Hessian `∇²_yy ℒ(y_opt, Y)` positive definite (17), then problem (16)
satisfies the quadratic growth condition at `y_opt`. Standing assumptions: `c ≠ 0` and
`F₀, …, F_m` symmetric (p. 33). -/
theorem theorem_4_1 {m n p q : ℕ} (D : SDPData m n p q) (c : Fin m → ℝ) (hc : c ≠ 0)
    (hsym : D.Symmetric) (h1 : D.Slater) (h2 : D.InfCompact c)
    (yopt : (Fin m → ℝ) × ℝ) (hopt : D.IsOptimal c yopt) (hτ : 0 < yopt.2)
    (h17 : ∃ Y ∈ dualSet D c yopt.2 yopt, ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2 (lagrangian D c yopt.2 Y) yopt ![h, h]) :
    QGC16 D c yopt.2 yopt := by sorry

end RobustSDP.FullPert.Supplement
