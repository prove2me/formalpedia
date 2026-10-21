-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P15_proposition_3_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P15.proposition_3_2
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T09:44:36.581859+00:00
-- url     : https://prove2.me/theorems/0a02dc82-a07f-4e57-9c31-147abbf77189
-- title:
--   Proposition 3.2
-- statement:
--   For faithful positive functionals $\nu,\omega$ on a nonzero finite-dimensional complex Hilbert space, let $D$ be the minimal sum of errors over projection tests. On the Hilbert--Schmidt space put $\Delta_{\nu|\omega}(A)=\nu A\omega^{-1}$ and $\Omega_\omega=\omega^{1/2}$. Then
--
--   $$D(\nu,\omega)\le\langle\Omega_\omega,\Delta_{\nu|\omega}^{s}\Omega_\omega\rangle=\operatorname{Tr}(\nu^s\omega^{1-s})\quad(0\le s\le1),\qquad D(\nu,\omega)\ge\langle\Omega_\omega,\Delta_{\nu|\omega}(1+\Delta_{\nu|\omega})^{-1}\Omega_\omega\rangle.$$
--
--   The first pairing is evaluated by the source's trace identity; the second is represented by the actual finite superoperator. Neither functional is required to be normalized.
-- source:
--   Quantum Hypothesis Testing and Non-Equilibrium Statistical Mechanics, arXiv:1109.3804v2, PDF p. 13, Proposition 3.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator BoundedContinuousFunction

namespace QAlgorithms.Papers.Independent.Claimed50.P15

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3.2, both bounds with unnormalized faithful functionals,
arXiv:1109.3804v2, PDF p.13. The upper quadratic form is evaluated by the
trace identity on PDF p.12; the lower form uses the actual finite superoperator. -/
theorem proposition_3_2 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (nu omega : Matrix I I ℂ) (hnu : nu.PosDef) (homega : omega.PosDef) :
    (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → optimalError false nu omega ≤ (petzOverlap nu omega s : EReal)) ∧
    (resolventOverlap nu omega : EReal) ≤ optimalError false nu omega := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P15

end
