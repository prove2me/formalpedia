-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_constrained_success_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.constrained_success_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:06:31.94476+00:00
-- url     : https://prove2.me/theorems/bf7ecd4f-d335-461f-82df-25caa7886ded
-- title:
--   Optimal finite-n type-I minimum and its success exponent
-- statement:
--   Let ρ≠σ be density operators with nested supports and let r>0. Define αₙ,ᵣ as the attained minimum of Tr ρₙ(I−T) over 0≤T≤I with Tr σₙT≤e^{−nr}. Then
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
--   \lim_n\frac1n\log(1-\alpha_{n,r})=-H_r^*(\rho\Vert\sigma).
--   $$
--
--   This connects finite-copy constrained optimization to the asymptotic strong-converse trade-off.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 18, Lemma IV.17

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

/-- arXiv:1309.3228v5, PDF p.18: Optimal finite-n type-I minimum and its success exponent. The finite-n constraint and actual minimum attainment are explicit; this optimum differs from the sequence-based constraint defining B*. -/
theorem constrained_success_limit (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (r : ℝ) (hr : 0 < r) :
    (∀ n : ℕ, 1 ≤ n → ∃ T : Mat (Fin n → I), IsEffect T ∧
      accept sigma n T ≤ Real.exp (-(n : ℝ) * r) ∧ typeI rho n T = minTypeI rho sigma n r) ∧
    Tendsto (fun n => scaled n (logNonnegativeExtended (1 - minTypeI rho sigma (n + 1) r)))
      atTop (nhds (-Hstar rho sigma r)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
