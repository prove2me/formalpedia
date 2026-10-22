-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P30_gaussian_locc_reduction
-- name    : QAlgorithms.Papers.Independent.Gap48.P30.gaussian_locc_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:21:58.124984+00:00
-- url     : https://prove2.me/theorems/4b8c6193-b7d0-4b89-ad93-fee26fdfdce6
-- title:
--   Appendix 5c: deterministic Gaussian LOCC for two-mode squeezed vacuum
-- statement:
--   Fix $0<\lambda<1$ and $0\le T<1$. Starting from the two-mode squeezed vacuum $|\Psi_\lambda^{(0)}\rangle$, Bob mixes his mode with vacuum on a beam splitter of transmissivity $T$ and heterodynes the reflected mode. The outcome is $z\in\mathbb C$, with reference measure $d^2z/\pi$. The retained-mode instrument has coefficients
--
--   $$
--   \langle m|K_T(z)|n\rangle=
--   \begin{cases}e^{-|z|^2/2}\sqrt{\binom n{n-m}}\,(1-T)^{(n-m)/2}T^{m/2}\,\overline z^{\,n-m}/\sqrt{(n-m)!},&m\le n,\\0,&m>n.\end{cases}
--   $$
--
--   These are bounded operators and form a complete continuous instrument: for every Fock vector $u$, the integrand is measurable and integrable and $\int\|K_T(z)u\|^2\,d^2z/\pi=\|u\|^2$. There exist complex gains $a,b$, chosen before the outcome, such that the branch obtained by applying $D_A(a\overline z)\otimes D_B(bz)$ after $I\otimes K_T(z)$ obeys
--
--   $$
--   v_z=c_z|\Psi_{\sqrt T\lambda}^{(0)}\rangle\quad\text{for every }z,\qquad
--   \int\|v_z\|^2\,d^2z/\pi=1.
--   $$
--
--   Here $c_z$ is an unnormalized complex scalar; all local tensor operators and displacements are physically realized. Bob communicates $z$ so that Alice and Bob can perform their respective displacements.
--
--   This is the specific deterministic Gaussian LOCC protocol described by the authors, retaining the splitter and heterodyne instrument rather than unrestricted LOCC existence. The source leaves its numerical displacement gains unspecified.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, PDF p. 10, Appendix 5c, paragraph after (A.59)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- arXiv:1111.1986v1, PDF p.10, Appendix 5c. Bob's actual reflected-mode
heterodyne instrument, followed by Alice and Bob displacements proportional
to his communicated complex outcome, deterministically produces the weaker
squeezed vacuum. The source specifies no numerical gains, so they are
existentially constructed, before the measurement outcome. -/
theorem gaussian_locc_reduction (lambda T : ℝ)
    (hl : 0 < lambda) (hlu : lambda < 1) (hT : 0 ≤ T) (hTu : T < 1) :
    D.DisplacementRealized ∧
    (∀ z : ℂ, D.HasFockMatrix (heterodyneBob T z) (heterodyneMatrix T z) ∧
      TensorRealized 1 (heterodyneBob T z)) ∧
    (∀ u : D.Fock, AEStronglyMeasurable (fun z : ℂ => heterodyneBob T z u) D.coherentMeasure ∧
      Integrable (fun z : ℂ => ‖heterodyneBob T z u‖ ^ 2) D.coherentMeasure ∧
      (∫ z : ℂ, ‖heterodyneBob T z u‖ ^ 2 ∂D.coherentMeasure) = ‖u‖ ^ 2) ∧
    ∃ a b : ℂ,
      (∀ z : ℂ, TensorRealized (D.displacement (a * star z)) (D.displacement (b * z))) ∧
      AEStronglyMeasurable (fun z : ℂ => gaussianBranch lambda T a b z) D.coherentMeasure ∧
      Integrable (fun z : ℂ => ‖gaussianBranch lambda T a b z‖ ^ 2) D.coherentMeasure ∧
      (∫ z : ℂ, ‖gaussianBranch lambda T a b z‖ ^ 2 ∂D.coherentMeasure) = 1 ∧
      ∀ z : ℂ, ∃ c : ℂ,
        gaussianBranch lambda T a b z = c • squeezed 0 (Real.sqrt T * lambda) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P30

end
