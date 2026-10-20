-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_np_nonasymptotic_bounds
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.np_nonasymptotic_bounds
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:58:39.3076+00:00
-- url     : https://prove2.me/theorems/257b545c-1aef-457c-933a-1a251e877568
-- title:
--   Both nonasymptotic Neyman-Pearson bounds
-- statement:
--   Let ρ≠σ be density operators with nested supports. For any real a and integer n≥1, let Sₙ(a)={ρ^{⊗n}−e^{na}σ^{⊗n}>0}, and let φ(a)=sup_{s≥0}{as−F_{1+s}(ρ‖σ)}. Both bounds hold:
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   The rate transforms are $\psi(s)=F_{1+s}(\rho\Vert\sigma)$, $\varphi(a)=\sup_{s\geq0}\{as-\psi(s)\}$, and $\widetilde\psi(u)=(1-u)\psi(u/(1-u))$ for $0\leq u<1$.
--
--   $$
--   \frac1n\log\operatorname{Tr}\rho_nS_n(a)\leq-\varphi(a),\qquad\frac1n\log\operatorname{Tr}\sigma_nS_n(a)\leq-\{a+\varphi(a)\}.
--   $$
--
--   These finite-copy estimates precede the asymptotically exact Neyman–Pearson exponents.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 11, Lemma IV.3

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

/-- arXiv:1309.3228v5, PDF p.11: Both nonasymptotic Neyman-Pearson bounds. Strict-positive spectral tests give zero at a≥Dmax, and log zero is −infinity. n=0 is excluded. -/
theorem np_nonasymptotic_bounds (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (((n : ℝ)⁻¹ : ℝ) : EReal) * logNonnegativeExtended (accept rho n (npTest rho sigma n a)) ≤ -phi rho sigma a ∧
    (((n : ℝ)⁻¹ : ℝ) : EReal) * logNonnegativeExtended (accept sigma n (npTest rho sigma n a)) ≤
      -((a : EReal) + phi rho sigma a) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
