-- Prove2me | Theorems.Thm_TimeInconsLQ_MeanVariance_theorem_5_4
-- name    : TimeInconsLQ.MeanVariance.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:45.615256+00:00
-- url     : https://prove2.me/theorems/344a354d-df5e-4e87-a54c-90dd28fe8398
-- title:
--   Theorem 5.4 — the explicit equilibrium mean–variance strategy u* = −M⁻¹[(U − θμ₁e^{∫r})X* + Γθ + γ⁽²⁾]
-- statement:
--   Consider the mean–variance problem of §5: a complete market driven by a $d$-dimensional Brownian motion $W$ on $[0,T]$, with deterministic bounded interest rate $r$ and a progressively measurable, essentially bounded (possibly random) risk premium $\theta$; the wealth under a strategy $u$ follows $dX_s=r_sX_s\,ds+\theta_s'u_s\,ds+u_s'\,dW_s$, $X_0=x_0$, and at each time $t$ the investor minimizes
--   $$J(t,x_t;u)=\tfrac12\mathrm{Var}_t(X_T)-(\mu_1x_t+\mu_2)E_t[X_T],\qquad\mu_1\ge0,$$
--   a risk aversion that depends on the current wealth $x_t$.
--
--   Let $(M,U)$ be the solution of the BSDE (5.8) in $L^\infty_{\mathcal F}\times L^2_{\mathcal F}$ with $M\ge c>0$, let $(\Gamma^{(2)},\gamma^{(2)})$ be the solution of (5.13) in $L^\infty_{\mathcal F}\times L^2_{\mathcal F}$, and $\Gamma_s=-\mu_2e^{\int_s^Tr_t\,dt}$. Then
--   $$u^*_s=-M_s^{-1}\Big[\big(U_s-\theta_s\mu_1e^{\int_s^Tr_v\,dv}\big)X^*_s+\Gamma_s\theta_s+\gamma^{(2)}_s\Big]$$
--   is an equilibrium strategy (Definition 2.1). Precisely: the closed-loop wealth equation under this feedback has a solution $X^*$, and for every such solution the strategy $u^*$ is an open-loop equilibrium of the problem.
--
--   The result gives the equilibrium of a mean–variance investor with state-dependent risk aversion in closed form, in terms of two BSDEs, even though the risk premium is random.
--
--   **Formalization Note.** The strategy is written as $u^*_s=\alpha_sX^*_s+\beta_s$ with $\alpha_s=(\Gamma^{(1)}_s\theta_s-U_s)/M_s$, $\beta_s=-(\Gamma_s\theta_s+\gamma^{(2)}_s)/M_s$ and $\Gamma^{(1)}_s=\mu_1e^{\int_s^Tr}$ (5.14), which is the printed formula. "The solutions" is read as *every* solution in the classes of Propositions 5.1–5.2 (no BMO property is assumed; it is a consequence). Existence of the closed-loop wealth is part of the conclusion. "Equilibrium" is Definition 2.1 on the LQ instance of the problem, with the shared conventions of the module `Model` (lower limit along every sequence $\varepsilon_k\downarrow0$, natural Brownian filtration, full-horizon state).
-- source:
--   Hu, Jin, Zhou, Time-Inconsistent Stochastic Linear–Quadratic Control, arXiv:1111.0818v1, p. 21, Theorem 5.4

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_TimeInconsLQ_MeanVariance_Model
import Definitions.Def_TimeInconsLQ_MeanVariance_Market

namespace TimeInconsLQ.MeanVariance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal Matrix

/-- Theorem 5.4 (p. 21). Let `(M, U)` solve (5.8) in the class of Proposition 5.1 and
`(Γ⁽²⁾, γ⁽²⁾)` solve (5.13) in the class of Proposition 5.2. Then the closed-loop wealth equation
under `u*_s = α_s X*_s + β_s = −M_s⁻¹[(U_s − θ_s μ₁ e^{∫ₛᵀ r}) X*_s + Γ_s θ_s + γ⁽²⁾_s]` has a
solution, and for every solution `X*` the control `u*` is an equilibrium (Definition 2.1) of the
mean–variance problem (5.2)–(5.3). -/
theorem theorem_5_4 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (mk : Market Ω d)
    (hmk : mk.Standing)
    (M : ℝ≥0 → Ω → ℝ) (U : ℝ≥0 → Ω → Fin d → ℝ) (hMU : mk.Class58 M U)
    (Γ2 : ℝ≥0 → Ω → ℝ) (γ2 : ℝ≥0 → Ω → Fin d → ℝ) (hΓ : mk.Class513 M U Γ2 γ2) :
    (∃ X, mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X) ∧
    ∀ X, mk.mvData.IsClosedLoop (mk.alpha M U) (mk.beta M γ2) X →
      mk.mvData.IsEquilibrium (mk.uStar M U γ2 X) := by sorry

end TimeInconsLQ.MeanVariance
