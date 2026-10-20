-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_cutoff_operational_formula
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.cutoff_operational_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:07:03.483661+00:00
-- url     : https://prove2.me/theorems/c52fd591-2a87-478c-9b85-4f1f2446807c
-- title:
--   The generalized cutoff rate is the new Renyi divergence
-- statement:
--   For distinct density operators with nested supports and κ∈(0,1), let Cκ be the smallest real r₀ such that, for every r>0, limsup n⁻¹ log(1−αₙ,ᵣ)≤−κ(r−r₀), where αₙ,ᵣ is the finite-n constrained minimum. Then
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Write $H_r^*=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}[r-\widetilde D_\alpha]$. For tests $0\leq T_n\leq I$ on $n$ copies, success is $\operatorname{Tr}\rho^{\otimes n}T_n$ and type-II error is $\beta_n=\operatorname{Tr}\sigma^{\otimes n}T_n$. The operational exponent is $B_e^*(r)=\inf_{(T_n):\,\limsup_n n^{-1}\log\beta_n\leq-r}\{-\liminf_n n^{-1}\log\operatorname{Tr}\rho^{\otimes n}T_n\}$.
--
--   $$
--   C_\kappa(\rho\Vert\sigma)=\widetilde D_{1/(1-\kappa)}(\rho\Vert\sigma).
--   $$
--
--   The least cutoff intercept supplies a direct operational characterization of the divergence.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 19, Theorem IV.18

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

/-- arXiv:1309.3228v5, PDF p.19: The generalized cutoff rate is the new Renyi divergence. Leastness is an explicit conclusion in addition to the infimum equality. The theorem starts on PDF p.19, following the cutoff definition on p.18. -/
theorem cutoff_operational_formula (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (kappa : ℝ) (hk0 : 0 < kappa) (hk1 : kappa < 1) :
    cutoff rho sigma kappa = Dnew (1 / (1 - kappa)) rho sigma ∧
    IsLeast {r0 : ℝ | CutoffBound rho sigma kappa r0}
      (Dnew (1 / (1 - kappa)) rho sigma).toReal := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
