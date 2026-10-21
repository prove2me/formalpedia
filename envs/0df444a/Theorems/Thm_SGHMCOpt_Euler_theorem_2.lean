-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_theorem_2
-- name    : SGHMCOpt.Euler.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:37.979673+00:00
-- url     : https://prove2.me/theorems/52f5094f-0957-48e4-87c9-4b772d90860c
-- title:
--   Theorem 2, pp. 10–11 — |∫F_z dμ_{k,z} − ∫F_z dπ_z| ≤ 𝒥₀(z,ε) + 𝒥₁(ε) for the SGHMC1 iterates
-- statement:
--   Consider the SGHMC1 iterates $(X_k,V_k)$ of (1.8)–(1.9) for a fixed dataset $z$, started from $(X_0,V_0)\sim\mu_0$, under Assumption 1, the parameter conditions, the drift condition (2.2) with constant $A>0$ and the pair $(\alpha_1,\Lambda)$ of (A.15). Write $\mu_{k,z}$ for the law of $(X_k,V_k)$ and $\pi_z$ for the Gibbs law (1.7). There is a function $h$ of the class on p. 39 such that for every $\varepsilon>0$, every step size $\eta$ with
--   $$\eta\le\min\Big\{\Big(\frac{\varepsilon}{(\log(1/\varepsilon))^{3/2}}\Big)^4,\ 1,\ \frac\gamma{K_2}\Big(\frac d\beta+\frac A\beta\Big),\ \frac{\gamma\lambda}{2K_1},\ \frac2{\gamma\lambda}\Big\}\quad(3.3)$$
--   and every $k$ with $k\eta=\frac1{\mu_*}\log\frac1\varepsilon\ge e$ (3.4),
--   $$\Big|\int F_z(x)\,\mu_{k,z}(dx,dv)-\int F_z(x)\,\pi_z(dx,dv)\Big|\le\mathcal J_0(z,\varepsilon)+\mathcal J_1(\varepsilon),$$
--   where $\mathcal J_0(z,\varepsilon)=(M\sigma+B)\,C\sqrt{\mathcal H_\rho(\mu_0,\pi_z)}\,\varepsilon$ (3.1), $\mathcal H_\rho$ is built from this $h$, and $\mathcal J_1$ is (3.2); all constants are those of Table 1.
--
--   The first term measures the dependence on the initialisation through the contraction of the underdamped Langevin dynamics, the second the discretisation error and the gradient noise.
--
--   **Formalization Note** The constants are evaluated at the exact integrals $\int\mathcal V\,d\mu_0$ and $\int e^{\alpha\mathcal V/4}d\mu_0$ for the Lyapunov function of $z$, and $C_1$ is the corrected constant described in `SGHMCOpt.Euler.Constants`. The function $h$ is existential, as in Theorem 19 (Eberle–Guillin–Zimmer), which the proof uses; $\alpha_1$ and $\varepsilon_1$ are pinned to (A.15), (A.16). The conclusion also asserts that $\mathcal H_\rho(\mu_0,\pi_z)$ is finite (so its real value is meaningful) and that $F_z(x)$ is integrable under both laws. $\varepsilon<1$ is implied by (3.4).
-- source:
--   arXiv:1809.04618v4, Theorem 2, (3.1)–(3.4), pp. 10–11; Theorem 19, p. 39; Table 1, p. 13

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model
import Definitions.Def_SGHMCOpt_Euler_Transport

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Theorem 2, pp. 10–11: for a fixed dataset `z`, there is a function `h` of the class on p. 39
(with `R₁` of (A.17); `α₁`, `ε₁` are those of (A.15), (A.16)) such that for every `ε > 0`, every
`η` with (3.3) and every `k` with (3.4),
`|∫ F_z(x) μ_{k,z}(dx, dv) − ∫ F_z(x) π_z(dx, dv)| ≤ 𝒥₀(z, ε) + 𝒥₁(ε)`.
The constants use `∫ 𝒱 dμ₀` and `∫ e^{α𝒱/4} dμ₀` for the Lyapunov function of `z`, and the
corrected `C₁`. -/
theorem theorem_2 {d n : ℕ} {𝒵 𝒰 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒰]
    [MeasurableSpace Ω] (f : E d → 𝒵 → ℝ) (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰)
    (μ0 : Measure (E d × E d)) (P : Measure Ω) (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d)
    (U : ℕ → Ω → 𝒰) (p : Params) (hn : 0 < n)
    (hloss : LossAssumption f p) (horacle : OracleAssumption f g νU p)
    (hinit : InitAssumption n f μ0 p) (hpar : ParamCond p) (hdrift : DriftCond n f p)
    (hfix : FixedPt p d) (hnoise : SGHMC1Noise P X0 V0 ξ U μ0 νU) (z : Fin n → 𝒵) :
    ∃ h : ℝ → ℝ, IsEGZProfile h (R1 p d) ∧
      ∀ (ε η : ℝ) (k : ℕ), 0 < ε → StepCond p d ε η → KCond p ε η k →
        Hrho p h f z μ0 (gibbs p f z) ≠ ⊤ ∧
        Integrable (fun q : E d × E d => Fz f z q.1) (lawSGHMC1 P g z p η X0 V0 ξ U k) ∧
        Integrable (fun q : E d × E d => Fz f z q.1) (gibbs p f z) ∧
        |∫ q, Fz f z q.1 ∂(lawSGHMC1 P g z p η X0 V0 ξ U k) - ∫ q, Fz f z q.1 ∂(gibbs p f z)| ≤
          J0 p d (∫ q, lyap p f z q.1 q.2 ∂μ0) (Hrho p h f z μ0 (gibbs p f z)).toReal ε +
            J1 p d (∫ q, lyap p f z q.1 q.2 ∂μ0)
              (∫ q, Real.exp (alpha p / 4 * lyap p f z q.1 q.2) ∂μ0) ε := by sorry

end SGHMCOpt.Euler
