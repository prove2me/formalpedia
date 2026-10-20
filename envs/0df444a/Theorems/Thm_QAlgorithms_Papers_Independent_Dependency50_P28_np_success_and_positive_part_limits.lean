-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_np_success_and_positive_part_limits
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.np_success_and_positive_part_limits
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:59:43.083819+00:00
-- url     : https://prove2.me/theorems/935a9ba7-d03d-48c4-93fa-a2ee08dc1855
-- title:
--   Success and positive-part exponents in the interior range
-- statement:
--   Let ρ≠σ be density operators with nested supports, and choose D(ρ‖σ)<a<Dmax(ρ‖σ). For the specific strict Neyman–Pearson test Sₙ(a) and the positive Jordan part (·)₊,
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   The rate transforms are $\psi(s)=F_{1+s}(\rho\Vert\sigma)$, $\varphi(a)=\sup_{s\geq0}\{as-\psi(s)\}$, and $\widetilde\psi(u)=(1-u)\psi(u/(1-u))$ for $0\leq u<1$.
--
--   $$
--   \lim_n\frac1n\log\operatorname{Tr}\rho_nS_n(a)=\lim_n\frac1n\log\operatorname{Tr}(\rho_n-e^{na}\sigma_n)_+=-\varphi(a).
--   $$
--
--   The common exponent describes both test success and the positive-part trace in the interior range.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 11, Theorem IV.4

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

/-- arXiv:1309.3228v5, PDF p.11: Success and positive-part exponents in the interior range. Both limits are separate conclusions. When D=Dmax the stipulated interval is legitimately empty. -/
theorem np_success_and_positive_part_limits (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (a : ℝ)
    (hlo : relativeEntropy rho sigma < (a : EReal)) (hhi : (a : EReal) < Dmax rho sigma) :
    Tendsto (fun n => scaled n (logNonnegativeExtended (accept rho (n + 1) (npTest rho sigma (n + 1) a))))
      atTop (nhds (-phi rho sigma a)) ∧
    Tendsto (fun n => scaled n (logNonnegativeExtended (tr (positivePart
      (copies (n + 1) rho - (Real.exp (((n + 1 : ℕ) : ℝ) * a) : ℂ) • copies (n + 1) sigma)))))
      atTop (nhds (-phi rho sigma a)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
