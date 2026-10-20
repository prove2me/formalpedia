-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_strong_converse_exponent
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.strong_converse_exponent
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:03:20.03438+00:00
-- url     : https://prove2.me/theorems/278c2d36-3dcc-4a74-a8d1-4de7556b3ed8
-- title:
--   Exact strong converse exponent in quantum hypothesis testing
-- statement:
--   Let ρ≠σ be density matrices on a finite-dimensional complex Hilbert space, with supp ρ contained in supp σ. For a real rate r≥0, optimize over all sequences of binary tests accepting ρ. The strong converse exponent uses the limsup type-II exponent constraint and minus the liminf success exponent. It is exactly
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
--   B_e^*(r)=H_r^*(\rho\Vert\sigma)=\sup_{\alpha>1}\frac{\alpha-1}{\alpha}\bigl[r-\widetilde D_\alpha(\rho\Vert\sigma)\bigr].
--   $$
--
--   This is the paper’s exact operational strong-converse exponent formula.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 15, Theorem IV.10

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

/-- arXiv:1309.3228v5, PDF p.15: Exact strong converse exponent in quantum hypothesis testing. Seed node retained for Theorem IV.10, (87), on PDF p.15. The flat case D=Dmax is included; its omission from the printed proof does not invalidate the theorem. -/
theorem strong_converse_exponent (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (r : ℝ) (hr : 0 ≤ r) :
    strongExponent rho sigma r = Hstar rho sigma r := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
