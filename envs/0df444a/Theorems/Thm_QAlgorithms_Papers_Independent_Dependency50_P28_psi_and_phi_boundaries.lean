-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_psi_and_phi_boundaries
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.psi_and_phi_boundaries
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:57:21.603362+00:00
-- url     : https://prove2.me/theorems/784ca0aa-fff2-4654-9700-b9499df8c7a5
-- title:
--   Derivatives of psi and all three branches of phi
-- statement:
--   Let ρ≠σ be density operators with nested supports. Define ψ(s)=F_{1+s}(ρ‖σ) and φ(a)=sup_{s≥0}{as−ψ(s)}, and write D and Dmax for Umegaki and max-relative entropy of this pair. Then
--
--   Write $Q_\alpha(\rho\Vert\sigma)=\operatorname{Tr}(\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)})^\alpha$ and $F_\alpha=\log Q_\alpha$. Powers are evaluated only on positive eigenvalues and are zero on the kernel, even at exponent zero; scalar logarithms satisfy $\log0=-\infty$.
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   The rate transforms are $\psi(s)=F_{1+s}(\rho\Vert\sigma)$, $\varphi(a)=\sup_{s\geq0}\{as-\psi(s)\}$, and $\widetilde\psi(u)=(1-u)\psi(u/(1-u))$ for $0\leq u<1$.
--
--   $$
--   \psi(0)=0,\quad\psi^{\prime}(0)=D,\quad\lim_{s\to\infty}\psi^{\prime}(s)=D_{\max};\qquad\varphi(a)=0\ (a\leq D),\quad\varphi(a)>0\ (D<a\leq D_{\max}),\quad\varphi(a)=+\infty\ (a>D_{\max}).
--   $$
--
--   These identities identify the thresholds and effective domain of the rate transform.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 10, Lemma IV.2 We have

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

/-- arXiv:1309.3228v5, PDF p.10: Derivatives of psi and all three branches of phi. psi is real only on the legitimate state/support domain; phi remains EReal. No D<Dmax premise is imposed; its middle branch can be empty. -/
theorem psi_and_phi_boundaries (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma)
    (hsupp : SupportLE rho sigma) (hne : rho ≠ sigma) :
    psi rho sigma 0 = 0 ∧
    HasDerivAt (psi rho sigma) (relativeEntropy rho sigma).toReal 0 ∧
    Tendsto (deriv (psi rho sigma)) atTop (nhds (Dmax rho sigma).toReal) ∧
    (∀ a : ℝ, (a : EReal) ≤ relativeEntropy rho sigma → phi rho sigma a = 0) ∧
    (∀ a : ℝ, relativeEntropy rho sigma < (a : EReal) →
      (a : EReal) ≤ Dmax rho sigma → 0 < phi rho sigma a) ∧
    (∀ a : ℝ, Dmax rho sigma < (a : EReal) → phi rho sigma a = ⊤) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
