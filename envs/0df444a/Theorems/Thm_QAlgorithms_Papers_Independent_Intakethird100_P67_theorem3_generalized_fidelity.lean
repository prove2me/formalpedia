-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_theorem3_generalized_fidelity
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.theorem3_generalized_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T08:53:37.976072+00:00
-- url     : https://prove2.me/theorems/75a4d130-4476-4eed-a110-f4574c45f0e5
-- title:
--   Theorem 3: generalized emulation fidelity and conditional fidelity
-- statement:
--   Let $\Lambda$ be a finite nonempty parameter set with probability distribution $p$, and let $W_{\rm in}(\lambda)$ be arbitrary system/one-qubit unitaries. Fix a unit anchor $\phi$, an ambient unitary $U$, and $T\ge0$. Use independent parameters with law $p$, $T$ ancillas initially in $\lvert-\rangle$, output anchor $U\phi$, and $W_{\rm out}(\lambda)=(U\otimes I)W_{\rm in}(\lambda)(U^\dagger\otimes I)$. Let $\mathcal E_U$ and $\Sigma_U$ be the main and joint outputs of the four Appendix-A steps, ignoring the measurement label, and let $p_{\rm erase}(\rho)=\langle\phi|\mathcal W^T(\rho)|\phi\rangle$. For every input density operator,
--
--   $$F(\Sigma_U(\rho),U\rho U^\dagger\otimes\lvert-\rangle\langle-\rvert^{\otimes T})\ge p_{\rm erase}(\rho),\qquad F(\mathcal E_U(\rho),U\rho U^\dagger)\ge p_{\rm erase}(\rho).$$
--
--   For a pure input and positive erasure probability, the normalized successful output has root fidelity at least $\sqrt{p_{\rm erase}(\rho)}$ with $U\rho U^\dagger$. No supported-input or algebra-generation assumption is needed. These estimates include the working ancillas before tracing.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 13, Theorem 3: generalized emulation fidelity and conditional fidelity

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF pp.13–16, Theorem 3: root fidelity for actual Fig.5, including the joint
output and positive-probability pure-input conditional output. A1's missing adjoint is
corrected by Eq.(18) and A12; no algebra or input-support promise is assumed here. -/
theorem theorem3_generalized_fidelity [Nonempty L] (p : L → ℝ)
    (hp : QAlgorithms.Learning.IsDistribution p) (W : L → Matrix.unitaryGroup (I × Bool) ℂ)
    (phi : EuclideanSpace ℂ I) (hphi : IsState phi) (U : Matrix.unitaryGroup I ℂ) (T : ℕ) :
    (∀ rho, IsDensityMatrix rho →
      let joint := jointEmulator p (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ))
        (transportedGate (U : Matrix I I ℂ) (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ)))
        phi (act (U : Matrix I I ℂ) phi) T rho
      let pe := eraseProbability p (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ)) phi T rho
      pe ≤ rootFidelity joint (Matrix.kronecker (densityConjugation (U : Matrix I I ℂ) rho)
          (pureDensity (minusRegister T))) ∧
        pe ≤ rootFidelity (traceRight joint) (densityConjugation (U : Matrix I I ℂ) rho)) ∧
    (∀ psi : EuclideanSpace ℂ I, IsState psi →
      let pe := eraseProbability p (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ)) phi T (pureDensity psi)
      0 < pe → Real.sqrt pe ≤ rootFidelity
        ((pe : ℂ)⁻¹ • traceRight (jointBranch p (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ))
          (transportedGate (U : Matrix I I ℂ) (fun l => (W l : Matrix (I × Bool) (I × Bool) ℂ)))
          phi (act (U : Matrix I I ℂ) phi) T false (pureDensity psi)))
        (densityConjugation (U : Matrix I I ℂ) (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
