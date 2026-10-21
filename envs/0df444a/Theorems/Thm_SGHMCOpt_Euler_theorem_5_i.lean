-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_theorem_5_i
-- name    : SGHMCOpt.Euler.theorem_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:14.779068+00:00
-- url     : https://prove2.me/theorems/e8f70580-b5cf-4333-a399-c474085c4df8
-- title:
--   Theorem 5 (first inequality), p. 14 — generalization error of SGHMC1: |E F(X_k) − E F(X_π)| ≤ 𝒥̄₀(ε) + 𝒥₁(ε)
-- statement:
--   Assume the setting of Theorem 2, a probability law $D$ on $\mathcal Z$ and a sample $Z\sim D^n$. Let $\overline V_0$ and $\overline E_0$ satisfy $\int\mathcal V_z\,d\mu_0\le\overline V_0$ and $\int e^{\alpha\mathcal V_z/4}d\mu_0\le\overline E_0$ for every dataset $z$, where $\mathcal V_z$ is the Lyapunov function of $z$. If $\varepsilon>0$, $\eta$ satisfies (3.3) and $k$ satisfies (3.4), then
--   $$\big|\mathbb EF(X_k)-\mathbb EF(X_\pi)\big|\le\overline{\mathcal J}_0(\varepsilon)+\mathcal J_1(\varepsilon),$$
--   where $\mathbb EF(X_k)=\int D^n(dz)\,\mathbb E_z[F(X_k)]$ is taken over the sample and the algorithm's randomness, $X_\pi$ has conditional law $\pi_z$ given $Z=z$, so $\mathbb EF(X_\pi)=\int D^n(dz)\int F(x)\pi_z(dx,dv)$, and $\overline{\mathcal J}_0(\varepsilon)=(M\sigma+B)\,C\sqrt{\overline{\mathcal H}_\rho(\mu_0)}\,\varepsilon$ (3.6).
--
--   This bounds the first term of the decomposition (A.21) of the population risk in the proof of Corollary 4.
--
--   **Formalization Note** The constants $\sigma$, $C_0$, $C_1$, $C_2$ depend on $\int\mathcal V_z\,d\mu_0$ and $\int e^{\alpha\mathcal V_z/4}d\mu_0$, which depend on the dataset, yet the paper writes $\mathcal J_1(\varepsilon)$ outside the expectation over $Z$; they are evaluated here at the uniform bounds $\overline V_0$, $\overline E_0$ (every constant increases in both). $\overline{\mathcal H}_\rho(\mu_0)$ has the corrected coefficient of Lemma 20. All integrability facts are part of the conclusion. Only the first inequality of Theorem 5 is stated.
-- source:
--   arXiv:1809.04618v4, Theorem 5, p. 14; (3.6), p. 12; first term of (A.21), proof of Corollary 4, p. 41

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Theorem 5 (first inequality), p. 14: under the setting of Theorem 2, with `V̄₀` and `Ē₀`
bounds on `∫ 𝒱 dμ₀` and `∫ e^{α𝒱/4} dμ₀` uniform in the dataset, and provided (3.3) and (3.4),
`|E F(X_k) − E F(X_π)| ≤ 𝒥̄₀(ε) + 𝒥₁(ε)`, where both expectations are also over the sample
`Z ∼ Dⁿ`, and `X_π | Z = z` has the law `π_z`. -/
theorem theorem_5_i {d n : ℕ} {𝒵 𝒰 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒰]
    [MeasurableSpace Ω] (f : E d → 𝒵 → ℝ) (D : Measure 𝒵) [IsProbabilityMeasure D]
    (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰)
    (μ0 : Measure (E d × E d)) (P : Measure Ω) (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d)
    (U : ℕ → Ω → 𝒰) (p : Params) (hn : 0 < n)
    (hloss : LossAssumption f p) (horacle : OracleAssumption f g νU p)
    (hinit : InitAssumption n f μ0 p) (hpar : ParamCond p) (hdrift : DriftCond n f p)
    (hfix : FixedPt p d) (hnoise : SGHMC1Noise P X0 V0 ξ U μ0 νU)
    (V0bar E0bar : ℝ) (hV0 : ∀ z : Fin n → 𝒵, ∫ q, lyap p f z q.1 q.2 ∂μ0 ≤ V0bar)
    (hE0 : ∀ z : Fin n → 𝒵, ∫ q, Real.exp (alpha p / 4 * lyap p f z q.1 q.2) ∂μ0 ≤ E0bar)
    (ε η : ℝ) (k : ℕ) (hε : 0 < ε) (hstep : StepCond p d ε η) (hk : KCond p ε η k) :
    (∀ z : Fin n → 𝒵, Integrable (fun ω => F f D (sghmc1 g z p η X0 V0 ξ U k ω).1) P) ∧
      (∀ z : Fin n → 𝒵, Integrable (fun q : E d × E d => F f D q.1) (gibbs p f z)) ∧
      Integrable (fun z : Fin n → 𝒵 => ∫ ω, F f D (sghmc1 g z p η X0 V0 ξ U k ω).1 ∂P)
        (Measure.pi fun _ : Fin n => D) ∧
      Integrable (fun z : Fin n → 𝒵 => ∫ q, F f D q.1 ∂(gibbs p f z))
        (Measure.pi fun _ : Fin n => D) ∧
      |∫ z, ∫ ω, F f D (sghmc1 g z p η X0 V0 ξ U k ω).1 ∂P ∂(Measure.pi fun _ : Fin n => D) -
          ∫ z, ∫ q, F f D q.1 ∂(gibbs p f z) ∂(Measure.pi fun _ : Fin n => D)| ≤
        J0bar p d V0bar (∫ q, (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) ∂μ0) ε + J1 p d V0bar E0bar ε := by sorry

end SGHMCOpt.Euler
