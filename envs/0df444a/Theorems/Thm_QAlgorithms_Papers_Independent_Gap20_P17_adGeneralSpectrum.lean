-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P17_adGeneralSpectrum
-- name    : QAlgorithms.Papers.Independent.Gap20.P17.adGeneralSpectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:47:11.430093+00:00
-- url     : https://prove2.me/theorems/0fcbe0a3-5e76-46df-af3d-999f37245920
-- title:
--   AD general input, phase invariance, joint output and spectra
-- statement:
--   Let $\eta,p\in[0,1]$, $\theta\in[0,\pi]$, and $\phi\in\mathbb R$. Alice prepares the normalized state
--
--   $$|\psi\rangle=\sqrt{1-p}|0_R0_A\rangle+\sqrt p\,e^{i\phi}(\cos\theta|0_R1_A\rangle+\sin\theta|1_R1_A\rangle).$$
--
--   Its input marginal has diagonal $(1-p,p)$ and upper off-diagonal $\sqrt{(1-p)p}e^{-i\phi}\cos\theta$. The actual AD joint output equals the Eq.(16) block matrix, in Bob-first order; its phase is generated from the zero-phase matrix by $\operatorname{diag}(1,e^{i\phi})$ on Bob and hence leaves joint entropy unchanged. Define
--
--   $$\ell_\pm(x)=\frac{1\pm\sqrt{(1-2xp)^2+4x(1-p)p\cos^2\theta}}2.$$
--
--   The reference spectrum is $\ell_\pm(1)$, the joint spectrum is $\{\ell_+(1-\eta),\ell_-(1-\eta),0,0\}$, and Bob's spectrum is $\ell_\pm(\eta)$. At zero phase Bob has diagonal $(1-\eta p,\eta p)$ and off-diagonal $\sqrt{\eta(1-p)p}\cos\theta$. These identities supply the entropy formulas for general inputs.
-- source:
--   Reverse Coherent Information, arXiv:0808.0210v2, PDF p. 5, Eqs.(14)–(21), pp.4–5

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P17

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap20.P17

open scoped Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel IsDegradable IsAntidegradable dilationPower)

open QAlgorithms.Papers.Independent.Dependency50.P09 (erasureFin entangledPhi tensorAction)

open QAlgorithms.Papers.Independent.Claimed50.P24 (productDilation)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4–5, Eqs.(14)–(21): normalized constructed AD input/output, corrected
positive phase unitary, phase-invariant joint entropy, and all marginal spectra.
Displayed joint coordinates are Bob first, as in (16). -/
theorem adGeneralSpectrum (eta p theta phi : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (htheta : theta ∈ Set.Icc (0 : ℝ) Real.pi) :
    ‖inputPurification p theta phi‖ = 1 ∧
    generalInput p theta phi =
      !![((1-p : ℝ) : ℂ), (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (-Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ);
        (Real.sqrt ((1-p)*p) : ℂ) *
          Complex.exp (Complex.I * (phi : ℂ)) * (Real.cos theta : ℂ), (p : ℂ)] ∧
    (let U : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal
       ![1, Complex.exp (Complex.I * (phi : ℂ))]
     dampingJointOutput (adChannel eta) p theta phi =
       conjSuperop (Matrix.kronecker U (1 : Matrix (Fin 2) (Fin 2) ℂ))
         (gadBlockMatrix eta 0 p theta)) ∧
    vnEntropy (dampingJointOutput (adChannel eta) p theta phi) =
      vnEntropy (dampingJointOutput (adChannel eta) p theta 0) ∧
    HasSpectrum (traceLeft (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues 1 p theta) ∧
    HasSpectrum (dampingJointOutput (adChannel eta) p theta phi) (adJointEigenvalues eta p theta) ∧
    traceRight (dampingJointOutput (adChannel eta) p theta 0) =
      !![((1-eta*p : ℝ) : ℂ), ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ);
        ((Real.sqrt (eta*(1-p)*p)*Real.cos theta : ℝ) : ℂ), ((eta*p : ℝ) : ℂ)] ∧
    HasSpectrum (traceRight (dampingJointOutput (adChannel eta) p theta phi))
      (adEigenvalues eta p theta) := by sorry

end QAlgorithms.Papers.Independent.Gap20.P17

end
