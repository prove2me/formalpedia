-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P25_pure_input_trace_power_contraction
-- name    : QAlgorithms.Papers.Independent.Advance50.P25.pure_input_trace_power_contraction
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:53:37.080608+00:00
-- url     : https://prove2.me/theorems/a8dbdd65-8630-430a-936b-be3fd6e6fd13
-- title:
--   Pure-input trace-power contraction under channels
-- statement:
--   Let $\mathcal E$ be any completely positive trace-preserving channel between finite-dimensional complex systems. Let $\phi$ and $\psi$ be unit input vectors, and put $\rho=|\phi\rangle\langle\phi|$ and $\sigma=|\psi\rangle\langle\psi|$. For an operator $X$, define $|X|=(X^\dagger X)^{1/2}$. Then, for every real $q\ge1$,
--
--   $$
--   \operatorname{Tr}|\rho-\sigma|^q\ge
--   \operatorname{Tr}|\mathcal E(\rho)-\mathcal E(\sigma)|^q.
--   $$
--
--   In particular, with $D_{\mathrm{HS}}(\tau,\omega)=\operatorname{Tr}[(\tau-\omega)^2]$,
--
--   $$
--   D_{\mathrm{HS}}(\rho,\sigma)\ge
--   D_{\mathrm{HS}}(\mathcal E(\rho),\mathcal E(\sigma)).
--   $$
--
--   The two input vectors need not be orthogonal, and the channel outputs may be mixed. This contraction result concerns pure inputs and uses the trace power without taking a $q$th root.
-- source:
--   Non-negative discord strengthens the subadditivity of quantum entropy functions, arXiv:1101.1717v1, PDF p. 4, Lemma 4 (§V): pure-input trace-power contraction under channels

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P25

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Advance50.P25

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw average entropy)

open QAlgorithms.Papers.Independent.Claimed50.P48 (nonzeroSpectrum)

open QAlgorithms.Papers.Independent.Gap48.P33 (discardLast)

/-- PDF p.4, Lemma 4: pure-input trace-power contraction for every real q ≥ 1,
and its squared Hilbert–Schmidt specialization. No purity of the outputs is assumed. -/
theorem pure_input_trace_power_contraction {I O : Type}
    [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (E : Superop I O) (hE : IsChannel E)
    (phi psi : EuclideanSpace ℂ I) (hphi : ‖phi‖ = 1) (hpsi : ‖psi‖ = 1) :
    (∀ q : ℝ, 1 ≤ q →
      finiteTraceMoment q (matrixAbsolute (E (pureDensity phi) - E (pureDensity psi))) ≤
        finiteTraceMoment q (matrixAbsolute (pureDensity phi - pureDensity psi))) ∧
    hilbertSchmidtDistance (E (pureDensity phi)) (E (pureDensity psi)) ≤
      hilbertSchmidtDistance (pureDensity phi) (pureDensity psi) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P25

end
