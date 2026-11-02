-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P75_bell_exact_and_robust
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P75.bell_exact_and_robust
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:02:47.688396+00:00
-- url     : https://prove2.me/theorems/11ae272c-2506-419e-b2dd-890434ccd81b
-- title:
--   Exact and robust self-testing of entangled two-qubit states
-- statement:
--   Let \(0\leq\theta\leq\pi/4\). Define the unit target and Bell parameter by
--   \[
--   |\psi_\theta\rangle=\cos\theta|00\rangle+\sin\theta|11\rangle,\qquad
--   \alpha(\theta)=\frac{2\cos(2\theta)}{\sqrt{1+\sin^2(2\theta)}},\qquad
--   b(\alpha)=\sqrt{8+2\alpha^2}.
--   \]
--   Then \(0\leq\alpha(\theta)\leq2\). The concrete qubit strategy \(A_0=Z,A_1=X\), \(B_0=\cos\mu Z+\sin\mu X,B_1=\cos\mu Z-\sin\mu X\), with Pauli matrices \(X,Z\) and \(\mu=\arctan(\sin(2\theta))\), consists of dichotomic observables and attains \(b(\alpha(\theta))\) on this target.
--
--   Let \(H_A,H_B\) be arbitrary complex Hilbert spaces, \(|\psi'\rangle\) a unit vector in their completed Hilbert tensor product, and \(A_0,A_1,B_0,B_1\) bounded self-adjoint involutions on the indicated local spaces. Set
--   \[
--   \mathcal B_\alpha=\alpha A_0\otimes I+
--    A_0\otimes(B_0+B_1)+A_1\otimes(B_0-B_1).
--   \]
--   If its expectation on \(\psi'\) equals \(b(\alpha(\theta))\), there exist local complex-linear isometric embeddings \(\Phi_A,\Phi_B\) and normalized, possibly entangled junk with
--   \[
--   (\Phi_A\otimes\Phi_B)|\psi'\rangle
--   =|\mathrm{junk}\rangle\otimes|\psi_\theta\rangle.
--   \]
--   For each fixed \(0<\theta\leq\pi/4\), for every \(\eta>0\) there is a \(\delta>0\), depending only on \(\theta,\eta\), such that every realization above with Bell expectation at least \(b(\alpha(\theta))-\delta\) admits such embeddings and junk satisfying
--   \[
--   \|(\Phi_A\otimes\Phi_B)|\psi'\rangle-
--   |\mathrm{junk}\rangle\otimes|\psi_\theta\rangle\|\leq\eta.
--   \]
--   Equalities and norms use one fixed regrouping of physical and added registers. This certifies the state, without a measurement-intertwining claim. The endpoint \(\theta=0,\alpha=2\) is retained in the exact clause as product extraction.
--
--   **Formalization Note** The printed tangent relation is corrected to a double-angle relation via the continuous parameter formula above. In particular, \(\alpha=0\) gives \(\theta=\pi/4\). The qualitative robustness clause does not assert the defective explicit coefficients.
-- source:
--   Robust Self Testing of Unknown Quantum Systems into Any Entangled Two-Qubit States, arXiv:1210.4409v2, PDF p. 2, §III, unnumbered Theorem: exact and robust self-testing of every pure entangled two-qubit state

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P75

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P75

universe u v w x

open QAlgorithms.Papers.Independent.Claimed50.P34 (HilbertTensor)

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

/-- PDF pp.2–3, unnumbered Theorem, with robustness in the sense of (3).
The printed Schmidt relation is corrected as documented at tiltParameter.
The ideal qubit strategy realizes every target nonvacuously. Exact extraction
includes theta=0,alpha=2 as the product branch. Robustness is fixed-theta and
uniform over arbitrary physical Hilbert spaces and all dichotomic observables.
No measurement-intertwining conclusion or invalid (19)–(20) estimate is added. -/
theorem bell_exact_and_robust (theta : ℝ) (htheta : 0 ≤ theta)
    (hthetaUpper : theta ≤ Real.pi / 4) :
    0 ≤ tiltParameter theta ∧ tiltParameter theta ≤ 2 ∧
    ‖schmidtTarget (qubitCoefficients theta)‖ = 1 ∧
    Dichotomic idealZ ∧ Dichotomic idealX ∧
    Dichotomic (idealB0 theta) ∧ Dichotomic (idealB1 theta) ∧
    bellValue (tiltParameter theta) idealZ idealX (idealB0 theta) (idealB1 theta)
      (schmidtTarget (qubitCoefficients theta)) = quantumMaximum (tiltParameter theta) ∧
    (∀ (H : Type u) (K : Type v)
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (psi : HilbertTensor H K) (A0 A1 : H →L[ℂ] H) (B0 B1 : K →L[ℂ] K),
      ‖psi‖ = 1 → Dichotomic A0 → Dichotomic A1 → Dichotomic B0 → Dichotomic B1 →
      bellValue (tiltParameter theta) A0 A1 B0 B1 psi =
        quantumMaximum (tiltParameter theta) →
      ExtractsWithin (qubitCoefficients theta) psi 0) ∧
    (0 < theta → ∀ eta : ℝ, 0 < eta → ∃ delta : ℝ, 0 < delta ∧
      ∀ (H : Type u) (K : Type v)
      [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
      (psi : HilbertTensor H K) (A0 A1 : H →L[ℂ] H) (B0 B1 : K →L[ℂ] K),
      ‖psi‖ = 1 → Dichotomic A0 → Dichotomic A1 → Dichotomic B0 → Dichotomic B1 →
      quantumMaximum (tiltParameter theta) - delta ≤
        bellValue (tiltParameter theta) A0 A1 B0 B1 psi →
      ExtractsWithin (qubitCoefficients theta) psi eta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P75

end
