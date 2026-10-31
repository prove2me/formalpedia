-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_elementaryPairInversions
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.elementaryPairInversions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:48:55.656997+00:00
-- url     : https://prove2.me/theorems/4285fd0a-e8a7-49df-8c7a-8e5b6587cb7a
-- title:
--   Elementary pair spectra and explicit reversing pulses
-- statement:
--   For real $a,b,c$, put $H(a,b,c)=aX\otimes X+bY\otimes Y+cZ\otimes Z$, where $X,Y,Z$ are the Pauli matrices. Its characteristic polynomial is
--
--   $$\chi_H(z)=(z-a-b+c)(z+a-b-c)(z-a+b-c)(z+a+b+c).$$
--
--   If $abc\ne0$, no special-unitary conjugation sends $H$ to $-H$, and it is not type-I locally reversible. A $\pi$ rotation about $x$ on either qubit reverses $Z\otimes Z$. A $\pi$ z-rotation on either qubit reverses $H(1,\kappa,0)$ for every real $\kappa$. Write $R_z(\theta)=e^{-i\theta Z/2}$. If $\beta_1+\beta_2$ is an odd multiple of $\pi$, then
--
--   $$\operatorname{Ad}_{R_z(\beta_1)\otimes R_z(-\beta_2)} H(1,1,0)=-H(1,1,0),\qquad
--   \operatorname{Ad}_{R_z(\beta_1)\otimes R_z(\beta_2)} H(1,-1,0)=-H(1,-1,0).$$
--
--   Here the paper's XX denotes XX+YY. These are the specified pulse constructions; the full generic transverse-axis subtype table is separately deferred.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 5, (24) and Table II: elementary pair spectra and explicit inversions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Table II and (24), PDF p.5. XX means XX+YY, and XY means XX+kappa YY.
The z-pulse angles are actual angles: the printed beta1(z1)-beta2(1z)
means theta1=beta1, theta2=-beta2. The full generic transverse-axis table
is deferred separately. Nonzero a,b,c are required for the obstruction. -/
theorem elementaryPairInversions :
    (∀ a b c : ℝ, (xyz a b c).charpoly =
      (Polynomial.X - Polynomial.C (a+b-c : ℂ)) *
      (Polynomial.X - Polynomial.C (-a+b+c : ℂ)) *
      (Polynomial.X - Polynomial.C (a-b+c : ℂ)) *
      (Polynomial.X - Polynomial.C (-a-b-c : ℂ))) ∧
    (∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      ¬ (∃ U : Matrix.specialUnitaryGroup (QAlgorithms.Qubits 2) ℂ,
        adjointConjugation (U : Op (QAlgorithms.Qubits 2)) (xyz a b c) = -xyz a b c)) ∧
    (∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → ¬ TypeI (xyz a b c)) ∧
    (∀ l : Fin 2,
      adjointConjugation (axisPulse 0 (fun k => if k = l then Real.pi else 0))
        (xyz 0 0 1) = -xyz 0 0 1) ∧
    (∀ kappa : ℝ, ∀ l : Fin 2,
      adjointConjugation (individualZRotation (fun k => if k = l then Real.pi else 0))
        (xyz 1 kappa 0) = -xyz 1 kappa 0) ∧
    (∀ beta1 beta2 : ℝ, OddPi (beta1 + beta2) →
      adjointConjugation (individualZRotation (fun l : Fin 2 => if l = 0 then beta1 else -beta2))
        (xyz 1 1 0) = -xyz 1 1 0) ∧
    (∀ beta1 beta2 : ℝ, OddPi (beta1 + beta2) →
      adjointConjugation (individualZRotation (fun l : Fin 2 => if l = 0 then beta1 else beta2))
        (xyz 1 (-1) 0) = -xyz 1 (-1) 0) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
