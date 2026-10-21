-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P06_integralFidelityUnderDomination
-- name    : QAlgorithms.Papers.Independent.Claimed50.P06.integralFidelityUnderDomination
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T09:07:02.07652+00:00
-- url     : https://prove2.me/theorems/1d78a86c-d908-4a77-aee0-f52c44893e53
-- title:
--   Integrated domination bounds the average fidelity
-- statement:
--   Let $\mathcal A$ act in standard form on a complex Hilbert space $\mathcal H$. Set $p(t)=\pi/(1+\cosh(2\pi t))$ and $d\mu(t)=p(t)\,dt$. Let $\sigma=\omega_s$ and $\rho=\omega_r$ be normal states represented by unit vectors $s,r\in\mathcal H$, where $\omega_v(a)=\langle v,av\rangle$. Let $\Upsilon,\Psi:\mathbb R\to\mathcal H$ be strongly continuous square-integrable functions for $\mu$. Suppose for every positive $a\in\mathcal A$ that
--
--   $$\int\omega_{\Upsilon_t}(a)\,d\mu(t)\le\sigma(a),\qquad
--   \int\omega_{\Psi_t}(a)\,d\mu(t)\le\rho(a).$$
--
--   The homogeneous unsquared fidelity $t\mapsto F(\omega_{\Upsilon_t},\omega_{\Psi_t})$ is continuous and integrable, and
--
--   $$\int_{\mathbb R} F(\omega_{\Upsilon_t},\omega_{\Psi_t})\,d\mu(t)\le F(\sigma,\rho).$$
--
--   This bounds an average of fiber fidelities using domination of the integrated functionals. Fiber vectors need not be unit vectors.
--
--   **Formalization Note** Positive operators are tested as $a^*a$. Fidelity is the supremum of $|\langle v,x'w\rangle|$ over contractions $x'$ in the concrete commutant. The integral is a genuine integrable real function, not a default value for a nonintegrable integrand.
-- source:
--   Approximate recovery and relative entropy I. general von Neumann subalgebras, arXiv:2006.08002v1, PDF p. 28, Lemma 10: integral fidelity under integrated domination

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P06

noncomputable section

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Claimed50.P06

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Lemma 10, PDF p.28, Eqs.(151)–(152); proof pp.28–29. The domination
hypotheses concern the integrated functionals. Fiber vectors may be unnormalized.
Unit vectors s and r represent sigma and rho. Testing a* a is equivalent to testing
all positive elements. Integrability of the fidelity is included so the displayed
integral cannot be a Bochner default on a nonintegrable function. -/
theorem integralFidelityUnderDomination
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (_form : StandardForm A)
    (s r : H) (hs : ‖s‖ = 1) (hr : ‖r‖ = 1)
    (upsilon psi : ℝ → H) (hUpsilon : Continuous upsilon) (hPsi : Continuous psi)
    (hUpsilonL2 : Integrable (fun t => ‖upsilon t‖ ^ 2) recoveryMeasure)
    (hPsiL2 : Integrable (fun t => ‖psi t‖ ^ 2) recoveryMeasure)
    (hDomSigma : ∀ a : A,
      (∫ t, (vectorFunctional (upsilon t) (star (a : (H →L[ℂ] H)) * a)).re
        ∂recoveryMeasure) ≤ (vectorFunctional s (star (a : (H →L[ℂ] H)) * a)).re)
    (hDomRho : ∀ a : A,
      (∫ t, (vectorFunctional (psi t) (star (a : (H →L[ℂ] H)) * a)).re
        ∂recoveryMeasure) ≤ (vectorFunctional r (star (a : (H →L[ℂ] H)) * a)).re) :
    Continuous (fun t => vectorFidelity A (upsilon t) (psi t)) ∧
    Integrable (fun t => vectorFidelity A (upsilon t) (psi t)) recoveryMeasure ∧
    (∫ t, vectorFidelity A (upsilon t) (psi t) ∂recoveryMeasure) ≤
      vectorFidelity A s r := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P06

end
