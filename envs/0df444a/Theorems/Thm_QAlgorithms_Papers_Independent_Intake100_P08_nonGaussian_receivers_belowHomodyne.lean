-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P08_nonGaussian_receivers_belowHomodyne
-- name    : QAlgorithms.Papers.Independent.Intake100.P08.nonGaussian_receivers_belowHomodyne
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:49:34.898874+00:00
-- url     : https://prove2.me/theorems/24bbc7d0-8f53-4d3c-8e66-e2231e7b2efe
-- title:
--   Both optimized non-Gaussian receivers beat ideal homodyne at every positive power
-- statement:
--   Let $\alpha>0$ be the known real amplitude of equiprobable coherent signals $|\pm\alpha\rangle$. Assume ideal optics and detection: $\eta=1$, $\nu=0$, and, for the displacement implementation, $\tau=\xi=1$. Each receiver uses one fixed preprocessing operation and one on/off detector, without feedback. Type I permits every single-mode affine Gaussian unitary, including complex displacement, phase rotation and squeezing; Type II permits every complex displacement.
--
--   Both operational optimization problems attain their minima. There are a Gaussian unitary $U_{\rm opt}$ and a real $\gamma_{\rm opt}>0$, globally optimal in their respective families, such that
--
--   $$
--   P_I(U_{\rm opt})\le P_D(\gamma_{\rm opt})<P_{\rm HD}(\alpha),\qquad
--   P_{\rm HD}(\alpha)=\frac1{\sqrt\pi}\int_{\sqrt2\alpha}^{\infty}e^{-x^2}\,dx
--   =\frac12\operatorname{erfc}(\sqrt2\alpha).
--   $$
--
--   Here the exact homodyne outcome law has means $\pm\sqrt2\alpha$ and physical quadrature variance $1/2$. The Gaussian tail is integrable. The inequalities establish the universal positive-power advantage of both receiver families. No strict advantage is asserted at zero power or for a fixed nonideal dark-counting detector.
--
--   **Formalization Note** Gaussian unitaries are genuine isometries of the completed Fock space characterized by their symplectic action on Weyl operators and an affine phase. This operational comparison does not use the inconsistent printed Type-I stationary equations.
-- source:
--   Discrimination of the binary coherent signal: Gaussian-operation limit and simple non-Gaussian near-optimal receivers, arXiv:0706.1038v3, PDF p. 5, Abstract; Section III, Fig. 3; conclusions p.6

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P08

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P08

open MeasureTheory

open scoped BigOperators

open QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock fockKet coherentKet coherentCoefficient CoherentRealized
   displacement DisplacementRealized)

/-- PDF pp.1,5--6, abstract and Fig.3: both optimized receiver families beat
homodyne at every strictly positive signal power, for ideal eta=1, nu=0 optics.
Type-I is optimized over the full affine Gaussian-unitary family; Type-II over
all complex displacements. Global minimizers are concluded, never postulated.
This operational statement does not use the inconsistent Type-I Eqs.(20),(22).
The Gaussian tail is integrable; homodyne is its spectral law, not r=infinity
inside a family of normalizable vectors. Equality at alpha=0 is covered by
the sanity example and the displacement result, not a strict claim here. -/
theorem nonGaussian_receivers_belowHomodyne
    (alpha : ℝ) (halpha : 0 < alpha) :
    CoherentRealized ∧ DisplacementRealized ∧
    Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) ∧
    ∃ (U : Fock ≃ₗᵢ[ℂ] Fock) (gamma : ℝ),
      IsGaussianUnitary U ∧ 0 < gamma ∧
      (∀ V : Fock ≃ₗᵢ[ℂ] Fock, IsGaussianUnitary V →
        receiverError alpha 1 0 (fun psi => U psi) ≤
          receiverError alpha 1 0 (fun psi => V psi)) ∧
      (∀ delta : ℂ, displacementError alpha 1 0 (gamma : ℂ) ≤
        displacementError alpha 1 0 delta) ∧
      receiverError alpha 1 0 (fun psi => U psi) ≤
        displacementError alpha 1 0 (gamma : ℂ) ∧
      displacementError alpha 1 0 (gamma : ℂ) < bpskHomodyneError alpha := by sorry

end QAlgorithms.Papers.Independent.Intake100.P08

end
