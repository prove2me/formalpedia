-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_two_basis_erasure
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.two_basis_erasure
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:03:03.965202+00:00
-- url     : https://prove2.me/theorems/74aab160-f0e1-45aa-852a-3d86867eda2e
-- title:
--   Appendix G3, Eq.(G11): exact erasure and reconstruction in conjugate bases
-- statement:
--   Let $d\ge1$, let $\theta_0,\ldots,\theta_{d-1}$ be an unknown orthonormal basis of the input span, and put $\alpha_j=d^{-1/2}\sum_k e^{2\pi i kj/d}\theta_k$. Initialize a $d$-dimensional auxiliary register in $|\Gamma\rangle=d^{-1/2}\sum_t|t\rangle$. Let $V_P,V_Q$ be the full controlled spectral exponentials of $P=\sum_k k|\theta_k\rangle\langle\theta_k|$ and $Q=\sum_j j|\alpha_j\rangle\langle\alpha_j|$, and let $F_-$ be the normalized negative-sign Fourier transform. For every normalized $\psi=\sum_k\psi_k\theta_k$ in the input span,
--
--   $$V_Q(I\otimes F_-)V_P(|\psi\rangle|\Gamma\rangle)=|\theta_0\rangle\otimes\sum_k\psi_k|k\rangle.$$
--
--   Replacing the erased system by $U\theta_0$ and applying the corresponding output-basis inverse product reconstructs $U\psi\otimes\Gamma$ exactly. The exponentials act as identity outside the sample span. This is an exact circuit identity, separate from sample-access runtime claims.
--
--   For every pair of conjugate-basis labels $j,\ell$, the same theorem retains the one-sample construction from p.29 footnote 3:
--
--   $$e^{i(2\pi(\ell-j)/d)P}\alpha_j=\alpha_\ell.$$
--
--   Thus one conjugate sample can be converted into each other conjugate sample using the displayed phase evolution; its sample-access runtime remains separately deferred.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 29, Appendix G3, Eq.(G11): exact erasure and reconstruction in conjugate bases

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.29–30, G11 and p.29 footnote 3: exact erasure, reconstruction, and
conversion of one Fourier-conjugate sample into every other conjugate sample.
Printed G7 omits normalization and has the wrong ket index; normalized G6 and G11
fix the normalized negative-sign DFT. The reconstruction sentence after G11 already
prints V_P_out-dagger (I tensor F_a-dagger) V_Q_out-dagger; the reverse product
retains those printed adjoints. Only G7 normalization and its ket index are corrected.
Full exponentials extend by identity off the span. -/
theorem two_basis_erasure {d : ℕ} (hd : 1 ≤ d) (theta : Fin d → EuclideanSpace ℂ I)
    (htheta : Orthonormal ℂ theta) (psi : EuclideanSpace ℂ I) (hpsi : IsState psi)
    (hsupport : psi ∈ Submodule.span ℂ (Set.range theta)) (U : Matrix.unitaryGroup I ℂ) :
    let alpha := conjugateBasis theta
    let coords : EuclideanSpace ℂ (Fin d) := WithLp.toLp 2 fun k => inner ℂ (theta k) psi
    let erase := basisPhase alpha * Matrix.kronecker (1 : Matrix I I ℂ) (negativeFourier d) * basisPhase theta
    let thetaout := fun k => act (U : Matrix I I ℂ) (theta k)
    let alphaout := conjugateBasis thetaout
    act erase (tensorVec psi (uniformAddress d)) = tensorVec (theta ⟨0, by omega⟩) coords ∧
    act ((basisPhase thetaout)ᴴ * Matrix.kronecker (1 : Matrix I I ℂ) (negativeFourier d)ᴴ *
      (basisPhase alphaout)ᴴ) (tensorVec (thetaout ⟨0, by omega⟩) coords) =
      tensorVec (act (U : Matrix I I ℂ) psi) (uniformAddress d) ∧
    (∀ j l : Fin d,
      act (positivePhaseEvolution (∑ k : Fin d, (k.val : ℂ) • pureDensity (theta k))
        (2 * Real.pi * ((l.val : ℝ) - (j.val : ℝ)) / d)) (alpha j) = alpha l) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
