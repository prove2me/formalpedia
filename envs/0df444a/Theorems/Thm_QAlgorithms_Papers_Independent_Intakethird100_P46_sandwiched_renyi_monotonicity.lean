-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P46_sandwiched_renyi_monotonicity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P46.sandwiched_renyi_monotonicity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:28:05.341167+00:00
-- url     : https://prove2.me/theorems/80f60d60-eeb5-4fe2-bd26-1691e274deae
-- title:
--   Sandwiched Rényi divergence decreases under positive trace-nonincreasing maps
-- statement:
--   Let $d,d'$ be finite dimensions and let $\Phi:M_d(\mathbb C)\to M_{d'}(\mathbb C)$ be complex-linear, with $\Phi(A)\ge0$ and $\operatorname{tr}\Phi(A)\le\operatorname{tr}A$ for every $A\ge0$. For every finite real $\alpha>1$ and arbitrary positive semidefinite $\rho,\sigma$,
--
--   $$D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\le D_\alpha(\rho\Vert\sigma).$$
--
--   On support inclusion, $D_\alpha(\rho\Vert\sigma)=\frac{1}{\alpha-1}\log\operatorname{tr}[(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha]$; otherwise it is $+\infty$. Negative powers use the inverse on the support. The natural logarithm is extended by $\log0=-\infty$, so zero inputs and the zero map are included, without division by $\operatorname{tr}\rho$. This extends data processing to maps with positivity alone, even when trace can decrease.
-- source:
--   Monotonicity of the Quantum Relative Entropy Under Positive Maps, arXiv:1512.06117v3, PDF p. 3, Theorem 2: sandwiched Rényi monotonicity under positive trace-nonincreasing maps

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Intakethird100.P46

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P13
  (IsTraceClass TraceClass IsPositive operatorTrace)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Bridge50.P49 (beigiSandwichedDivergence)

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Müller-Hermes–Reeb, arXiv:1512.06117v3, PDF p.3, Theorem 2, (5).
The accepted sandwiched divergence is unnormalized and has extended log(0)=-infinity.
The map may be merely positive; the input operators may be zero or singular. -/
theorem sandwiched_renyi_monotonicity (d e : ℕ)
    (Phi : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin e) (Fin e) ℂ)
    (hPhi : PositiveMatrixTraceNonincreasing Phi)
    (alpha : ℝ) (hAlpha : 1 < alpha)
    (rho sigma : Matrix (Fin d) (Fin d) ℂ)
    (hrho : rho.PosSemidef) (hsigma : sigma.PosSemidef) :
    beigiSandwichedDivergence alpha (Phi rho) (Phi sigma) ≤
      beigiSandwichedDivergence alpha rho sigma := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P46

end
