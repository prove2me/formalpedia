-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_np_beta_limit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.np_beta_limit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:00:26.700514+00:00
-- url     : https://prove2.me/theorems/f637728c-4eb4-489c-95e2-5ad78a06d4d4
-- title:
--   The type-II Neyman-Pearson exponent in the interior range
-- statement:
--   Let ρ≠σ be density operators with nested supports and let D(ρ‖σ)<a<Dmax(ρ‖σ). For Sₙ(a)={ρₙ−e^{na}σₙ>0},
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   The rate transforms are $\psi(s)=F_{1+s}(\rho\Vert\sigma)$, $\varphi(a)=\sup_{s\geq0}\{as-\psi(s)\}$, and $\widetilde\psi(u)=(1-u)\psi(u/(1-u))$ for $0\leq u<1$.
--
--   $$
--   \lim_n\frac1n\log\operatorname{Tr}\sigma_n S_n(a)=-\{\varphi(a)+a\}.
--   $$
--
--   This gives the matching type-II exponent for the same strict spectral tests.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 12, Theorem IV.5

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

/-- arXiv:1309.3228v5, PDF p.12: The type-II Neyman-Pearson exponent in the interior range. Both endpoint inequalities are strict; at a=Dmax the strict spectral test is zero. -/
theorem np_beta_limit (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (a : ℝ)
    (hlo : relativeEntropy rho sigma < (a : EReal)) (hhi : (a : EReal) < Dmax rho sigma) :
    Tendsto (fun n => scaled n (logNonnegativeExtended (accept sigma (n + 1) (npTest rho sigma (n + 1) a))))
      atTop (nhds (-(phi rho sigma a + (a : EReal)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
