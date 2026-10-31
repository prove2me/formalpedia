-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_fermionic_covariance
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.fermionic_covariance
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:14:52.573772+00:00
-- url     : https://prove2.me/theorems/b6ddc32d-cf9b-4935-abaf-19984289a766
-- title:
--   Fermionic two-point covariance and bound
-- statement:
--   Let $Y$ be a real Hilbert space and $\phi:Y\to B(H)$ a real-linear self-adjoint CAR representation with $\{\phi(x),\phi(y)\}=2\langle x,y\rangle1$. Let $\Psi$ be a normalized fermionic quasi-free state vector, meaning its odd moments vanish and its even moments satisfy the signed Wick pairing rule. Define the real antisymmetric covariance by
--   $$\omega(x,y)=\frac1i\langle\Psi,[\phi(x),\phi(y)]\Psi\rangle.$$
--   Then
--   $$\langle\Psi,\phi(x)\phi(y)\Psi\rangle=\langle x,y\rangle+\frac i2\omega(x,y),\qquad |\omega(x,y)|\le2\sqrt{|\langle x,x\rangle|}\sqrt{|\langle y,y\rangle|}.$$
--   This fixes the covariance convention for the fermionic realization theorems. **Formalization Note** Normalization is the explicit source correction authorized in the plan; the printed Wick-only wording admits the zero vector. The coefficient $i/2$ is confirmed by rendering PDF p.46. The real part in the definition only packages the real-valued quantity in (83).
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 46, Theorem 42

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section FermionicCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- PDF p.46, Theorem 42: the coefficient is i/2 (verified in the PDF),
and the bound is 2. The explicitly corrected normalized quasi-free convention
is essential; no covariance symmetry or moment identity is assumed as data. -/
theorem fermionic_covariance (phi : E → H →L[ℂ] H) (hphi : IsCAR phi)
    (v : H) (hq : FermionicQuasiFree phi v) :
    (∀ x y, inner ℂ v ((phi x * phi y) v) = (inner ℝ x y : ℂ) +
      (Complex.I / 2) * (carCovariance phi v x y : ℂ)) ∧
    (∀ x y, |carCovariance phi v x y| ≤ 2 * Real.sqrt |inner ℝ x x| * Real.sqrt |inner ℝ y y|) := by sorry

end FermionicCovariance

end QAlgorithms.Papers.Independent.Intake100.P23

end
