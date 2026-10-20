-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_optimal_test_sequence
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.optimal_test_sequence
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:03:53.76803+00:00
-- url     : https://prove2.me/theorems/26ec14eb-2e45-49c4-ba8a-2c5b5d8dbb74
-- title:
--   An optimal test sequence with exact beta limsup
-- statement:
--   For distinct density operators ρ,σ with nested supports and every r≥0, there exists a sequence of valid effects Tₙ on n copies such that the type-II logarithmic limsup equals the target rate and the success logarithmic liminf attains the optimal exponent:
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
--   \limsup_n\frac1n\log\operatorname{Tr}\sigma_nT_n=-r,\qquad\liminf_n\frac1n\log\operatorname{Tr}\rho_nT_n=-H_r^*(\rho\Vert\sigma).
--   $$
--
--   The statement asserts actual optimal-sequence attainment while retaining the source’s distinct asymptotic limit notions.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 16, Remark IV.11 It is easy to see, by applying a standard diagonal argument, that there exists a sequence

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

/-- arXiv:1309.3228v5, PDF p.16: An optimal test sequence with exact beta limsup. The final sentence upgrading beta to equality is included. Success remains a liminf, not a limit. -/
theorem optimal_test_sequence (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (r : ℝ) (hr : 0 ≤ r) :
    ∃ T : TestSequence I,
      Filter.limsup (fun n => scaled n (logNonnegativeExtended (accept sigma (n + 1) (T n).1))) atTop = -(r : EReal) ∧
      Filter.liminf (fun n => scaled n (logNonnegativeExtended (accept rho (n + 1) (T n).1))) atTop = -Hstar rho sigma r := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
