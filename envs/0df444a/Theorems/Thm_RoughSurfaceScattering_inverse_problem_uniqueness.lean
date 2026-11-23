-- Prove2me | Theorems.Thm_RoughSurfaceScattering_inverse_problem_uniqueness
-- name    : RoughSurfaceScattering.inverse_problem_uniqueness
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T20:59:36.55203+00:00
-- url     : https://prove2.me/theorems/007f8ffa-3a29-4feb-8981-05eee26a0475
-- title:
--   Theorem 6.1: global uniqueness for the inverse problem from near-field data on a segment
-- statement:
--   For $m=1,2$ let $(\Gamma_{f_m},k_{m,-},k_+,\mu_m)$ be scatterers with a common, known upper wave number $k_+$, each satisfying the hypotheses of Theorem 5.2: $f_m\in BC^{1,1}(\mathbb R)\cap C^{2,\lambda_m}(\mathbb R)$ with $\lambda_m\in(0,1]$, $k_+,k_{m,-},\mu_m>0$, $(\mu_m-1)(k_+^2-k_{m,-}^2\mu_m)\ge0$ and $k_+^2\ne k_{m,-}^2\mu_m$. For $y\in D^+_m$ let $(u_{m,+}(\cdot,y),u_{m,-}(\cdot,y))$ solve the TSP for scatterer $m$ with incident point source $\Phi_{k_+}(\cdot,y)$. Let $d>0$, let $c>f_1^+$ and $c>f_2^+$, and let $\Gamma_{c,d}=\{(x_1,c):|x_1|\le d\}$. If
--
--   $$u_{1,+}(x,y)=u_{2,+}(x,y)\qquad\text{for all }x,y\in\Gamma_{c,d},$$
--
--   then $f_1=f_2$, $k_{1,-}=k_{2,-}$ and $\mu_1=\mu_2$.
--
--   So the unbounded rough interface, the transmission coefficient and the lower wave number are determined by near-field measurements at one frequency on one bounded segment above the interface, both for $\mu=1$ and $\mu\ne1$.
--
--   **Formalization Note** The paper states $c>f^+$ for a single interface; for two interfaces the segment must lie above both, which is the hypothesis used. The scattered fields are quantified over as families of TSP solutions indexed by the source point, unique by Theorem 3.3. Each interface may have its own Hölder exponent $\lambda_m$.
-- source:
--   C. Wu and J. Yang, Direct and inverse acoustic scattering by global rough surfaces, arXiv:2406.06129v2, claim c008; Section 6, Theorem 6.1, PDF p. 22 (measurement segment Γ_{c,d}: Section 6, p. 22)

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem inverse_problem_uniqueness (f1 f2 : ℝ → ℝ) (hf1 : IsBC1Alpha 1 f1) (hf2 : IsBC1Alpha 1 f2)
    (lam1 lam2 : ℝ) (hlam1 : 0 < lam1 ∧ lam1 ≤ 1) (hlam2 : 0 < lam2 ∧ lam2 ≤ 1)
    (hf1' : IsC2Lambda lam1 f1) (hf2' : IsC2Lambda lam2 f2)
    (kp k1 k2 μ1 μ2 : ℝ) (hpar1 : ParamCond kp k1 μ1) (hpar2 : ParamCond kp k2 μ2)
    (c d : ℝ) (hd : 0 < d) (hc1 : fsup f1 < c) (hc2 : fsup f2 < c)
    (U1 U2 : R2 → (R2 → ℂ) × (R2 → ℂ))
    (hU1 : ∀ y ∈ Dplus f1, IsTSPSolution f1 kp k1 μ1 (incData f1 (pointSource kp y)).1
      (incData f1 (pointSource kp y)).2 (U1 y).1 (U1 y).2)
    (hU2 : ∀ y ∈ Dplus f2, IsTSPSolution f2 kp k2 μ2 (incData f2 (pointSource kp y)).1
      (incData f2 (pointSource kp y)).2 (U2 y).1 (U2 y).2)
    (hdata : ∀ x ∈ measSeg c d, ∀ y ∈ measSeg c d, (U1 y).1 x = (U2 y).1 x) :
    f1 = f2 ∧ k1 = k2 ∧ μ1 = μ2 := by sorry

end RoughSurfaceScattering
