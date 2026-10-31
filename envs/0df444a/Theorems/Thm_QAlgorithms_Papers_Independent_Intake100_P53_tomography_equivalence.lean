-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P53_tomography_equivalence
-- name    : QAlgorithms.Papers.Independent.Intake100.P53.tomography_equivalence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:43:55.066083+00:00
-- url     : https://prove2.me/theorems/72e4750a-a6f2-4af9-be56-54c05d937904
-- title:
--   §III–IV: complete tomography fixes Eve up to purification equivalence
-- statement:
--   Let $\kappa>0$, $0<\eta\le1$, and $\delta\ge0$ be finite real parameters. Alice modulates normalized oscillator coherent states with density $\exp(-|\alpha|^2/(2\kappa))/(2\pi\kappa)$ relative to planar Lebesgue measure. Bob's tomographically verified output is $D(\sqrt\eta\alpha)\tau_{\delta/2}D(\sqrt\eta\alpha)^\dagger$, where $\tau_n$ is the thermal state of mean photon number $n$, and he uses ideal heterodyne detection. Bits are the signs of the real parts, with bit zero for a nonnegative real part. Public announcements are $a=(u,y)=(|\Re\alpha|,\Im\alpha)$ and $b=(w,z)=(|\Re\beta|,\Im\beta)$. Zero-real-part events have probability zero. All formulas below concern the source's collective-attack, infinite-key setting with completed tomography; they assert no finite-sample or coherent-attack security.
--
--   Let $V$ and $W$ be two fixed pure isometric dilations with the specified receiver on every coherent probe. Eve retains the full supported environment in each dilation. For a signal $\alpha$ and heterodyne outcome $\beta$, form the unnormalized branch $B_V(\alpha,\beta)=(\langle\beta|\otimes I)V|\alpha\rangle$ and its normalized vector $\epsilon_V=B_V/\|B_V\|$. Let $E_V$ be the closed linear span of these conditional vectors, and define $E_W$ similarly. The vectors are normalized, the two branch norms agree, and there is one common support isometry $U:E_V\to E_W$, onto $E_W$, such that
--
--   $$U\epsilon_V(\alpha,\beta)=\epsilon_W(\alpha,\beta),\qquad U B_V(\alpha,\beta)=B_W(\alpha,\beta)\quad(\alpha,\beta\in\mathbb C).$$
--
--   Thus the whole labelled ensemble, and hence Eve's knowledge after the same public announcements, is independent of the compatible purification. Arbitrary unused ancillary dimensions require support equivalence rather than a unitary between unequal ambient spaces.
-- source:
--   Security of coherent state quantum cryptography in the presence of Gaussian noise, arXiv:quant-ph/0608015v4, PDF p. 3, §III–IV: complete tomography fixes Eve up to purification equivalence

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P53

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P53

open MeasureTheory

open QAlgorithms.Papers.Independent.Dependency50.P39

open scoped ComplexConjugate Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.2--3, III--IV: complete tomography determines the entire labelled
Eve ensemble through one common support isometry, including all mixtures and
information about the signals. No equal-dimension ambient-unitary assertion
or mere marginal eigenvalue equivalence replaces ensemble equivalence. -/
theorem tomography_equivalence (P : CoherentHeterodyneParameters) (V W : GaussianAttack P) :
    (∀ alpha beta, ‖eveVector V alpha beta‖ = 1 ∧ ‖eveVector W alpha beta‖ = 1) ∧
    (∀ alpha beta, ‖eveBranch V alpha beta‖ = ‖eveBranch W alpha beta‖) ∧
    ∃ U : eveSupport V ≃ₗᵢ[ℂ] eveSupport W,
      ∀ alpha beta,
        U (supportedVector V alpha beta) = supportedVector W alpha beta ∧
        U ((‖eveBranch V alpha beta‖ : ℂ) • supportedVector V alpha beta) =
          (‖eveBranch W alpha beta‖ : ℂ) • supportedVector W alpha beta := by sorry

end QAlgorithms.Papers.Independent.Intake100.P53

end
