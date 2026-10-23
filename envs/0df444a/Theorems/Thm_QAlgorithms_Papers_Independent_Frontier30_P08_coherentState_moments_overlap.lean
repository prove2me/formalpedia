-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P08_coherentState_moments_overlap
-- name    : QAlgorithms.Papers.Independent.Frontier30.P08.coherentState_moments_overlap
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T09:13:37.428977+00:00
-- url     : https://prove2.me/theorems/90ef564e-b560-47d8-a5fe-a763f621599e
-- title:
--   Coherent-state moments, completeness, and exact overlap
-- statement:
--   On the full one-mode oscillator Hilbert space $\ell^2(\mathbb N;\mathbb C)$ with number basis $|n\rangle$, each $\alpha\in\mathbb C$ determines a normalized coherent vector
--
--   $$|\alpha\rangle=e^{-|\alpha|^2/2}\sum_{n=0}^{\infty}\frac{\alpha^n}{\sqrt{n!}}|n\rangle.$$
--
--   It lies in the finite second-moment domain of $q=a+a^\dagger$ and $p=i(a^\dagger-a)$, satisfies $a|\alpha\rangle=\alpha|\alpha\rangle$, and its pure-state density has mean $(2\operatorname{Re}\alpha,2\operatorname{Im}\alpha)$ and covariance $I_2$. For every $\alpha,\beta\in\mathbb C$,
--
--   $$|\langle\beta|\alpha\rangle|^2=e^{-|\beta-\alpha|^2}.$$
--
--   The coherent family has dense complex linear span and is nonorthogonal. These facts describe its overcompleteness on the entire oscillator space, including the vacuum $\alpha=0$.
--
--   **Formalization Note** Quadrature moments use their Fock-coordinate quadratic forms on the finite second-moment domain, so no unbounded observable is declared to be a bounded operator.
-- source:
--   Gaussian Quantum Information, arXiv:1110.3234v1, PDF p. 7, §II.B.2 Eqs.(28)–(30): coherent state moments and overlap

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P08

open scoped BigOperators ComplexOrder ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P39 (Fock coherentCoefficient)

/-- PDF p.7, Eqs.(29)–(30) and adjacent moment and overcompleteness statements:
normalized coherent vectors exist on the full oscillator space, have physical means
(2 Re alpha, 2 Im alpha), vacuum covariance, and the exact overlap. The family has
 dense linear span. Coefficients identify each vector independently of all conclusions. -/
theorem coherentState_moments_overlap :
    (∀ alpha : ℂ, ∃ psi : Fock,
      HasCoherentCoefficients alpha psi ∧ ‖psi‖ = 1 ∧
      finitePureQuadratures psi ∧
      (∀ n, annihilationSequence psi n = alpha * psi n) ∧
      pureMean psi 0 = 2 * alpha.re ∧ pureMean psi 1 = 2 * alpha.im ∧
      pureQuadratureCovariance psi = 1) ∧
    (∀ alpha beta : ℂ, ∀ psi phi : Fock,
      HasCoherentCoefficients alpha psi → HasCoherentCoefficients beta phi →
      ‖inner ℂ phi psi‖ ^ 2 = Real.exp (-‖beta - alpha‖ ^ 2)) ∧
    Dense (↑(Submodule.span ℂ {psi : Fock | ∃ alpha : ℂ,
      HasCoherentCoefficients alpha psi}) : Set Fock) := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P08

end
