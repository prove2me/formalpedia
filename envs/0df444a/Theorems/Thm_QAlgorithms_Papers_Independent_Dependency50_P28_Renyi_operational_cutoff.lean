-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_Renyi_operational_cutoff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.Renyi_operational_cutoff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:07:39.662994+00:00
-- url     : https://prove2.me/theorems/7ca3bc7e-a6e1-4a37-9428-c58725128ed1
-- title:
--   Direct operational interpretation at each order
-- statement:
--   For distinct density operators with nested supports and every α>1, the normalized new Renyi divergence is the generalized cutoff rate with parameter κ=(α−1)/α, defined as the smallest intercept for the uniform-in-r logarithmic success bound:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Write $H_r^*=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}[r-\widetilde D_\alpha]$. For tests $0\leq T_n\leq I$ on $n$ copies, success is $\operatorname{Tr}\rho^{\otimes n}T_n$ and type-II error is $\beta_n=\operatorname{Tr}\sigma^{\otimes n}T_n$. The operational exponent is $B_e^*(r)=\inf_{(T_n):\,\limsup_n n^{-1}\log\beta_n\leq-r}\{-\liminf_n n^{-1}\log\operatorname{Tr}\rho^{\otimes n}T_n\}$.
--
--   $$
--   \widetilde D_\alpha(\rho\Vert\sigma)=C_{(\alpha-1)/\alpha}(\rho\Vert\sigma).
--   $$
--
--   This is the inverse parameterization of that operational cutoff interpretation.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 19, Corollary IV.19

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.19: Direct operational interpretation at each order. -/
theorem Renyi_operational_cutoff (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (alpha : ℝ) (ha : 1 < alpha) :
    Dnew alpha rho sigma = cutoff rho sigma ((alpha - 1) / alpha) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
