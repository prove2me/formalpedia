-- Prove2me | Theorems.Thm_RoughSurfaceScattering_interface_and_mu_uniqueness
-- name    : RoughSurfaceScattering.interface_and_mu_uniqueness
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T03:28:09.999979+00:00
-- url     : https://prove2.me/theorems/5915c309-86f1-491a-841c-b84666941cde
-- title:
--   Theorem 6.1, steps (i)–(ii): the scattered fields on $D_1^+\cap D_2^+$ determine the interface and $\mu$
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ be scatterers with a common upper wave number $k_+$, each satisfying the hypotheses of Theorem 5.2: $f_m\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda_m}(\mathbb R)$ with $\lambda_m\in(0,1]$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. Write $D_m^+=\{x:x_2>f_m(x_1)\}$ and, for $y\in D_m^+$, let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the Transmission Scattering Problem for scatterer $m$ with incident point source $\Phi_{k_+}(\cdot,y)$. If
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in D_1^+\cap D_2^+,$$
--
--   then
--
--   $$f_1=f_2\qquad\text{and}\qquad\mu_1=\mu_2 .$$
--
--   These are parts (i) and (ii) of the proof of Theorem 6.1, covering both $\mu_1,\mu_2\ne1$ and the case where one of the coefficients equals $1$. Together with the step that extends the measured data to $D_1^+\cap D_2^+$ and the determination of $k_-$, it yields the uniqueness of the inverse problem.
--
--   **Formalization Note** The scattered fields are quantified over as families of TSP solutions indexed by the source point, unique by Theorem 3.3, exactly as in the formal statement of Theorem 6.1. Equality of interfaces $\Gamma_{f_1}=\Gamma_{f_2}$ is stated as equality of the profile functions $f_1=f_2$. Each interface may have its own Hölder exponent $\lambda_m$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, Section 6, proof of Theorem 6.1, parts (i) and (ii), PDF pp. 22–25 (part (i): case mu_1, mu_2 ≠ 1, interior transmission problem (6.1) and estimate (6.2); part (ii): case mu_1 = 1 or mu_2 = 1, interior transmission problem (6.3)).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem interface_and_mu_uniqueness (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hagree : ∀ x ∈ Dplus f1 ∩ Dplus f2, ∀ y ∈ Dplus f1 ∩ Dplus f2, (U1 y).1 x = (U2 y).1 x) :
    f1 = f2 ∧ μ1 = μ2 := by sorry

end RoughSurfaceScattering
