-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P04_wernerOneCopy
-- name    : QAlgorithms.Papers.Independent.Information100.P04.wernerOneCopy
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:29:26.914101+00:00
-- url     : https://prove2.me/theorems/f86e0f87-9100-434b-bd52-f5453eacceda
-- title:
--   Exact optimum of the one-copy auxiliary Werner functional
-- statement:
--   Let $d\ge2$ be an integer and $p\in[1/2,1]$. Write $P_0=(I+F_d)/2$, $P_1=(I-F_d)/2$ for the symmetric and antisymmetric projections and $\rho_p=2(1-p)P_0/[d(d+1)]+2pP_1/[d(d-1)]$. Set $u=(d-1)/(d+1)$, $q=d/(d+1)$, $t=p+u(1-p)$, $c_0(\mu)=(d+1-d\mu)/2$, and $c_1(\mu)=(d-1-(d-2)\mu)/2$. For $0<\mu\le1$, define $J_0(\mu)=(1-p)\log_2((1-p)/c_0(\mu))+p\log_2(p/c_1(\mu))$ and $J_1(\mu)=(1-u)(1-p)\log_2((1-p)/c_0(\mu))+t\log_2(t/(\mu q))$, with zero-numerator terms zero. There is a unique $\mu_*\in(0,1]$ at which $J_0=J_1$, and
--
--   $$E_{d,\mathrm{PPT}}(\rho_p)\ge\widetilde L(\rho_p)=\sup_E\widetilde\ell(\rho_p,E)=J_0(\mu_*)=J_1(\mu_*).$$
--
--   The supremum is over all finite one-copy POVMs. It is attained by $((1-u\lambda_*)P_0,(1-\lambda_*)P_1,\lambda_*(P_1+uP_0))$, with zero effects deleted, where $\lambda_*=J_0'(\mu_*)/(J_0'(\mu_*)-J_1'(\mu_*))$ for $p>1/2$, and $\lambda_*=1$ at $p=1/2$. At $p=1/2$, $\mu_*=1$ and $\widetilde L=0$; at $p=1$, $\mu_*=(d+1)/(d+2)$ and $\widetilde L=\log_2((d+2)/d)$. This is a one-copy functional optimum, with an operational lower bound.
-- source:
--   On PPT entanglement distillation, arXiv:2610.12454v1, PDF p. 28, Proposition19

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Information100.P04

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 19, PDF p.28: unique crossing, exact one-copy functional optimum and
attaining three-ray POVM, with both endpoints. The operational quantity has a LOWER bound. -/
theorem wernerOneCopy (d : ℕ) (hd : 2 ≤ d) (p : ℝ) (hp : 1/2 ≤ p) (hp1 : p ≤ 1) :
    ∃ mu : ℝ, 0 < mu ∧ mu ≤ 1 ∧ wernerJ0 d p mu = wernerJ1 d p mu ∧
      (∀ x : ℝ, 0 < x → x ≤ 1 → wernerJ0 d p x = wernerJ1 d p x → x = mu) ∧
      LTilde (werner d p) = wernerJ0 d p mu ∧ LTilde (werner d p) ≤ distillable (werner d p) ∧
      (let lam := wernerLambda d p mu
       0 ≤ lam ∧ lam ≤ 1 ∧
       (∀ j, (wernerMeasurement d lam j).PosSemidef) ∧
       (∑ j, wernerMeasurement d lam j) = 1 ∧
       ellTilde (werner d p) (wernerMeasurement d lam) = LTilde (werner d p)) ∧
      (p = 1/2 → mu = 1 ∧ wernerLambda d p mu = 1 ∧ LTilde (werner d p) = 0) ∧
      (p = 1 → mu = ((d:ℝ)+1)/(d+2) ∧
        LTilde (werner d p) = Real.logb 2 (((d:ℝ)+2)/d)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P04

end
