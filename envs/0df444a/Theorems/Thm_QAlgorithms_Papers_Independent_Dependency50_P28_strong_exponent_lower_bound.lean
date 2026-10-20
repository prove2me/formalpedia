-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_strong_exponent_lower_bound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.strong_exponent_lower_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:01:21.500829+00:00
-- url     : https://prove2.me/theorems/3b109b0d-99ca-4455-98dd-215ba19e57a4
-- title:
--   Converse Hoeffding lower bound for the strong exponent
-- statement:
--   Let ρ≠σ be density operators with nested supports and let r≥0. Define B*ₑ(r) as the infimum over test sequences with limsup n⁻¹ log βₙ≤−r of minus the liminf of n⁻¹ log success. Define H*ᵣ=sup_{α>1}[(α−1)/α](r−D̃α(ρ‖σ)). Then
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The normalized new divergence is $\widetilde D_\alpha=(F_\alpha-\log\operatorname{Tr}\rho)/(\alpha-1)$ when the supports are nested or $0<\alpha<1$, and is $+\infty$ otherwise; the first argument has positive trace. For states the trace-normalizing term is zero.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   Write $H_r^*=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}[r-\widetilde D_\alpha]$. For tests $0\leq T_n\leq I$ on $n$ copies, success is $\operatorname{Tr}\rho^{\otimes n}T_n$ and type-II error is $\beta_n=\operatorname{Tr}\sigma^{\otimes n}T_n$. The operational exponent is $B_e^*(r)=\inf_{(T_n):\,\limsup_n n^{-1}\log\beta_n\leq-r}\{-\liminf_n n^{-1}\log\operatorname{Tr}\rho^{\otimes n}T_n\}$.
--
--   $$
--   B_e^*(r)\geq H_r^*(\rho\Vert\sigma).
--   $$
--
--   This is the converse inequality for the optimal strong-converse exponent.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 13, Lemma IV.7

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

/-- arXiv:1309.3228v5, PDF p.13: Converse Hoeffding lower bound for the strong exponent. The full infimum over effects and the asymmetric limsup/liminf convention are in the definitions. -/
theorem strong_exponent_lower_bound (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (r : ℝ) (hr : 0 ≤ r) :
    Hstar rho sigma r ≤ strongExponent rho sigma r := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
