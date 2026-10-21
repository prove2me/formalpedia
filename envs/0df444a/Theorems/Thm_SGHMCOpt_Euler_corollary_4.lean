-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_corollary_4
-- name    : SGHMCOpt.Euler.corollary_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:16.30367+00:00
-- url     : https://prove2.me/theorems/a7e4cad9-17ae-4b87-9092-7e429a95c960
-- title:
--   Corollary 4, p. 12 — SGHMC1 population risk: E F(X_k) − F* ≤ 𝒥̄₀(ε) + 𝒥₁(ε) + 𝒥₂ + 𝒥₃(n)
-- statement:
--   **Population risk minimisation with SGHMC1.** Let $f:\mathbb R^d\times\mathcal Z\to\mathbb R$, $d\ge1$, satisfy Assumption 1 (i)–(iii), let $D$ be a probability law on $\mathcal Z$, $F(x)=\mathbb E_{Z\sim D}f(x,Z)$ and $F^*=\min_xF(x)$. Run SGHMC1 (1.8)–(1.9) on a sample $Z\sim D^n$, $n\ge1$, from $(X_0,V_0)\sim\mu_0$, with an unbiased gradient oracle satisfying Assumption 1 (iv), and assume Assumption 1 (v), the parameter conditions $\gamma,\beta>0$, $0<\lambda<\min\{1/4,m/(M+\gamma^2/2)\}$, the drift condition (2.2) with constant $A>0$ and the pair $(\alpha_1,\Lambda)$ of (A.15). Let $\lambda_0>0$ be a lower bound of the uniform spectral gap $\lambda_*$ of (3.8), and let $\overline V_0$, $\overline E_0$ bound $\int\mathcal V_z\,d\mu_0$ and $\int e^{\alpha\mathcal V_z/4}d\mu_0$ uniformly over datasets $z$. If $\varepsilon>0$, $\eta$ satisfies (3.3) and $k$ satisfies (3.4), then
--   $$\mathbb EF(X_k)-F^*\le\overline{\mathcal J}_0(\varepsilon)+\mathcal J_1(\varepsilon)+\mathcal J_2+\mathcal J_3(n),$$
--   where the expectation is over both the sample and the algorithm's randomness, and
--   $$\overline{\mathcal J}_0(\varepsilon)=(M\sigma+B)\,C\sqrt{\overline{\mathcal H}_\rho(\mu_0)}\,\varepsilon,\qquad \mathcal J_2=\frac d{2\beta}\log\Big(\frac{eM}m\Big(\frac{b\beta}d+1\Big)\Big),\qquad \mathcal J_3(n)=\frac{4\beta c_{LS}}n\Big(\frac{M^2}m\Big(b+\frac d\beta\Big)+B^2\Big),$$
--   with $\mathcal J_1$ of (3.2), $c_{LS}=\frac{2m^2+8M^2}{m^2M\beta}+\frac1{\lambda_0}(\frac{6M(d+\beta)}m+2)$, and the constants of Table 1.
--
--   This is the paper's answer to the stochastic program (1.1): an explicit, non-asymptotic bound on the expected suboptimality of the SGHMC1 iterate for a non-convex population risk, decomposed into an initialisation term, a discretisation-and-noise term, the concentration of the Gibbs law and the generalisation error.
--
--   **Formalization Note** The left side is the lower Lebesgue integral of $F(X_k)\ge0$ over $D^n$ and the algorithm's probability space, so it cannot collapse to a junk value. The paper's constants depend on the dataset through $\int\mathcal V_z\,d\mu_0$ and $\int e^{\alpha\mathcal V_z/4}d\mu_0$; they are evaluated at the uniform bounds $\overline V_0$, $\overline E_0$ (every constant increases in both). $c_{LS}$ uses $\lambda_0\le\lambda_*$ in place of $\lambda_*$, which is the printed bound when $\lambda_0=\lambda_*$ and avoids $1/0$ if $\lambda_*=0$. $C_1$ and $\overline{\mathcal H}_\rho(\mu_0)$ are the corrected constants described in `SGHMCOpt.Euler.Constants`; the $C_1$ correction increases the bound, while the correction replacing $M$ by $\beta M$ in $\overline{\mathcal H}_\rho$ increases or decreases it according to $\beta$. $d\ge1$ and $n\ge1$ are implicit in the paper ($\mathcal J_2$ divides by $d$, $\mathcal J_3$ by $n$).
-- source:
--   arXiv:1809.04618v4, Corollary 4, (3.6)–(3.8), p. 12; proof, (A.21), pp. 41–42

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Corollary 4, p. 12: under the setting of Theorem 2, with `V̄₀`, `Ē₀` bounds on `∫ 𝒱 dμ₀` and
`∫ e^{α𝒱/4} dμ₀` uniform in the dataset, a lower bound `λ₀ > 0` of the uniform spectral gap,
and (3.3), (3.4), the expected population risk of the SGHMC1 iterate `X_k`, taken over the
sample `Z ∼ Dⁿ` and the algorithm's randomness, satisfies
`E F(X_k) − F* ≤ 𝒥̄₀(ε) + 𝒥₁(ε) + 𝒥₂ + 𝒥₃(n)`. -/
theorem corollary_4 {d n : ℕ} {𝒵 𝒰 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒰]
    [MeasurableSpace Ω] (f : E d → 𝒵 → ℝ) (D : Measure 𝒵) [IsProbabilityMeasure D]
    (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰)
    (μ0 : Measure (E d × E d)) (P : Measure Ω) (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d)
    (U : ℕ → Ω → 𝒰) (p : Params) (hd : 0 < d) (hn : 0 < n)
    (hloss : LossAssumption f p) (horacle : OracleAssumption f g νU p)
    (hinit : InitAssumption n f μ0 p) (hpar : ParamCond p) (hdrift : DriftCond n f p)
    (hfix : FixedPt p d) (lam0 : ℝ) (hlam0 : 0 < lam0) (hP : HasPoincare n f p lam0)
    (hnoise : SGHMC1Noise P X0 V0 ξ U μ0 νU)
    (V0bar E0bar : ℝ) (hV0 : ∀ z : Fin n → 𝒵, ∫ q, lyap p f z q.1 q.2 ∂μ0 ≤ V0bar)
    (hE0 : ∀ z : Fin n → 𝒵, ∫ q, Real.exp (alpha p / 4 * lyap p f z q.1 q.2) ∂μ0 ≤ E0bar)
    (ε η : ℝ) (k : ℕ) (hε : 0 < ε) (hstep : StepCond p d ε η) (hk : KCond p ε η k) :
    ∫⁻ z, ∫⁻ ω, ENNReal.ofReal (F f D (sghmc1 g z p η X0 V0 ξ U k ω).1) ∂P
        ∂(Measure.pi fun _ : Fin n => D) ≤
      ENNReal.ofReal (Fstar f D + J0bar p d V0bar (∫ q, (‖q.1‖ ^ 2 + ‖q.2‖ ^ 2) ∂μ0) ε +
        J1 p d V0bar E0bar ε + J2 p d + J3 p d lam0 n) := by sorry

end SGHMCOpt.Euler
