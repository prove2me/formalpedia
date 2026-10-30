-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P11_measuredEntropy_fidelityLowerBound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P11.measuredEntropy_fidelityLowerBound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:24:58.421867+00:00
-- url     : https://prove2.me/theorems/f703e7c9-d2c8-4f86-96d9-52f171308669
-- title:
--   Measured relative entropy bounds the unsquared fidelity penalty
-- statement:
--   Let $M$ be a $\sigma$-finite von Neumann algebra in standard form on a separable complex Hilbert space. Let $\rho,\sigma$ be normal states on $M$, with $\sigma$ faithful. Write
--   $$
--   S_{\mathrm{meas}}(\rho\mid\sigma)=\sup_{h=h^*\in M}\{\rho(h)-\log\sigma(e^h)\}.
--   $$
--   For unit vectors $\psi,\eta$ representing $\rho,\sigma$, let $F(\rho\mid\sigma)=\sup_{u'\in M',\,\|u'\|\le1}|\langle\psi,u'\eta\rangle|$ be their unsquared fidelity. Then
--   $$
--   S_{\mathrm{meas}}(\rho\mid\sigma)\ge-2\log F(\rho\mid\sigma).
--   $$
--   The logarithm is natural and the penalty is $+\infty$ when $F=0$. This relates measured distinguishability to fidelity without requiring $\rho$ to be faithful or either entropy to be finite.
-- source:
--   Trace- and improved data processing inequalities for von Neumann algebras, arXiv:2102.07479v2, PDF p. 17, Proposition 1

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P11

noncomputable section

open Filter

open scoped ENNReal

namespace QAlgorithms.Papers.Independent.Bridge50.P11

open QAlgorithms.Papers.Independent.Claimed50.P06
  (StandardForm IsNormalState IsFaithful IsSigmaFinite vectorFunctional vectorFidelity)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Proposition 1, PDF p.17; proof pp.17–18. The reference state sigma is
faithful; rho need not be. psi and eta are arbitrary normalized vector
representatives of these actual normal functionals. The fidelity is unsquared,
and its penalty is -2 log F, with value +infinity at F = 0. The supremum over
commutant contractions in the accepted definition equals Eq.(86)'s supremum
over norm-one elements by scaling. No natural-cone restriction on these
representatives is required. -/
theorem measuredEntropy_fidelityLowerBound [TopologicalSpace.SeparableSpace H]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (_hSigmaFinite : IsSigmaFinite A)
    (rho sigma : A →L[ℂ] ℂ)
    (_hRho : IsNormalState A rho) (_hSigma : IsNormalState A sigma)
    (_hFaithful : IsFaithful A sigma)
    (psi eta : H) (_hPsi : ‖psi‖ = 1) (_hEta : ‖eta‖ = 1)
    (_hRhoRep : ∀ a : A, rho a = vectorFunctional psi a)
    (_hSigmaRep : ∀ a : A, sigma a = vectorFunctional eta a) :
    -(2 * ENNReal.log (ENNReal.ofReal (vectorFidelity A psi eta))) ≤
      measuredEntropy A rho sigma := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P11

end
