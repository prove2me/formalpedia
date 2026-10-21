-- Prove2me | Theorems.Thm_SGHMCOpt_Euler_lemma_16_ii
-- name    : SGHMCOpt.Euler.lemma_16_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:08.942224+00:00
-- url     : https://prove2.me/theorems/d67aff10-5502-49cb-a188-ac771ca858c9
-- title:
--   Lemma 16(ii), p. 37 — uniform L² bounds on the SGHMC1 iterates: sup_j E_z‖X_j‖² ≤ C^d_x and sup_j E_z‖V_j‖² ≤ C^d_v
-- statement:
--   Fix a dataset $z\in\mathcal Z^n$ and let $(X_j,V_j)_{j\ge0}$ be the SGHMC1 iterates (1.8)–(1.9) started from $(X_0,V_0)\sim\mu_0$, under Assumption 1, the parameter conditions $\gamma,\beta>0$, $0<\lambda<\min\{1/4,m/(M+\gamma^2/2)\}$ and the drift condition (2.2) with constant $A>0$. If
--   $$0<\eta\le\min\Big\{\frac\gamma{K_2}\Big(\frac d\beta+\frac A\beta\Big),\ \frac{\gamma\lambda}{2K_1},\ \frac2{\gamma\lambda}\Big\},$$
--   with $K_1$, $K_2$ of (A.3), (A.4), then for every $j\ge0$
--   $$\mathbb E_z\|X_j\|^2\le C^d_x=\frac{\int\mathcal V\,d\mu_0+\frac{4(d+A)}\lambda}{\frac18(1-2\lambda)\beta\gamma^2},\qquad \mathbb E_z\|V_j\|^2\le C^d_v=\frac{\int\mathcal V\,d\mu_0+\frac{4(d+A)}\lambda}{\frac\beta4(1-2\lambda)}.$$
--
--   The iterates thus have second moments bounded uniformly in time, which is what allows the 2-Wasserstein comparison with the continuous dynamics in the proof of Theorem 2.
--
--   **Formalization Note** $\mathcal V$ is the Lyapunov function (2.1) of the fixed dataset $z$, and $\int\mathcal V\,d\mu_0$ is a genuine integral because of Assumption 1 (v). The expectations $\mathbb E_z$ are lower Lebesgue integrals over the probability space carrying the algorithm's randomness. The first entry of the minimum is encoded as $K_2\eta\le\gamma(d/\beta+A/\beta)$, so it imposes nothing when $K_2=0$. Only part (ii) of Lemma 16 is stated; part (i) concerns the underdamped Langevin SDE.
-- source:
--   arXiv:1809.04618v4, Lemma 16 (ii), (A.3)–(A.6), p. 37

import Mathlib
import Definitions.Def_SGHMCOpt_Euler_Constants
import Definitions.Def_SGHMCOpt_Euler_Model

open MeasureTheory

namespace SGHMCOpt.Euler

/-- Lemma 16 (ii), p. 37: for a fixed dataset `z` and `0 < η ≤ min{(γ/K₂)(d/β + A/β), γλ/(2K₁), 2/(γλ)}`,
the SGHMC1 iterates satisfy `sup_j E_z‖X_j‖² ≤ C^d_x` and `sup_j E_z‖V_j‖² ≤ C^d_v`, with
`∫ 𝒱 dμ₀` the exact integral of the Lyapunov function of `z`. -/
theorem lemma_16_ii {d n : ℕ} {𝒵 𝒰 Ω : Type*} [MeasurableSpace 𝒵] [MeasurableSpace 𝒰]
    [MeasurableSpace Ω] (f : E d → 𝒵 → ℝ) (g : (Fin n → 𝒵) → E d → 𝒰 → E d) (νU : Measure 𝒰)
    (μ0 : Measure (E d × E d)) (P : Measure Ω) (X0 V0 : Ω → E d) (ξ : ℕ → Ω → E d)
    (U : ℕ → Ω → 𝒰) (p : Params) (hn : 0 < n)
    (hloss : LossAssumption f p) (horacle : OracleAssumption f g νU p)
    (hinit : InitAssumption n f μ0 p) (hpar : ParamCond p) (hdrift : DriftCond n f p)
    (hnoise : SGHMC1Noise P X0 V0 ξ U μ0 νU) (z : Fin n → 𝒵) (η : ℝ) (hη : StepCondL16 p d η)
    (j : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (‖(sghmc1 g z p η X0 V0 ξ U j ω).1‖ ^ 2) ∂P ≤
        ENNReal.ofReal (Cxd p d (∫ q, lyap p f z q.1 q.2 ∂μ0)) ∧
      ∫⁻ ω, ENNReal.ofReal (‖(sghmc1 g z p η X0 V0 ξ U j ω).2‖ ^ 2) ∂P ≤
        ENNReal.ofReal (Cvd p d (∫ q, lyap p f z q.1 q.2 ∂μ0)) := by sorry

end SGHMCOpt.Euler
