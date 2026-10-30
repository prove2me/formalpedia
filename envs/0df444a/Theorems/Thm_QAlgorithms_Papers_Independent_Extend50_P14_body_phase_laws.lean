-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P14_body_phase_laws
-- name    : QAlgorithms.Papers.Independent.Extend50.P14.body_phase_laws
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:56:37.255218+00:00
-- url     : https://prove2.me/theorems/ca2459b1-4904-4656-9766-e322884d4807
-- title:
--   U(1) body-phase laws and calibration
-- statement:
--   For n≥1 qubits let Π_m project onto Hamming weight m, let C_l be the sum of all weight-l Pauli Z strings, and let c_l(m) be its integer eigenvalue on sector m. For a U(1)-invariant unitary V define Φ_l(V)=∑_m c_l(m)arg det(V_m), in the angle group ℝ/(2πℤ). For 0≤l≤n and invariant unitaries V,W,
--
--   $$\Phi_l(WV)=\Phi_l(W)+\Phi_l(V),\qquad\Phi_l(V^\dagger)=-\Phi_l(V).$$
--
--   Positive-body phases are invariant under V↦e^{iα}V. For every bit mask b and real α, Φ_l(e^{iαZ^b})=2^nα if l=w(b), and zero otherwise, modulo 2π. Every V in V_k has Φ_l(V)=0 for k<l≤n. Finally an integrable invariant Hermitian Hamiltonian H with its absolutely continuous propagator V on [0,T] satisfies
--
--   $$\Phi_l(V(T))=-\int_0^T\operatorname{Tr}(H(t)C_l)\,dt\pmod{2\pi}.$$
--
--   These identities calibrate the phases as locality observables.
-- source:
--   Restrictions on realizable unitary operations imposed by symmetry and locality, arXiv:2003.05524v3, PDF p. 3, II.B / D.1: l-body phases, additivity, global phase and locality

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P14

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P14

open scoped Classical Matrix ComplexConjugate Matrix.Norms.Frobenius

open MeasureTheory

-- Exact accepted aliases and physical operators, without local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Advance50.P49 (onWire multiSwap)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF pp.3,32, D7: composition, adjoint, positive-body global-phase
invariance, Pauli-string calibration, and locality, all modulo 2π. -/
theorem body_phase_laws (n : ℕ) (hn : 1 ≤ n) :
    (∀ (V W : QMat n), U1Unitary V → U1Unitary W → ∀ l ≤ n,
      u1BodyPhase (W*V) l = u1BodyPhase W l + u1BodyPhase V l ∧
      u1BodyPhase Vᴴ l = -u1BodyPhase V l) ∧
    (∀ (V : QMat n), U1Unitary V → ∀ (l : ℕ) (alpha : ℝ), 1 ≤ l → l ≤ n →
      u1BodyPhase (Complex.exp (Complex.I*alpha) • V) l = u1BodyPhase V l) ∧
    (∀ (b : Qubits n) (alpha : ℝ) (l : ℕ), l ≤ n →
      u1BodyPhase (schrodingerEvolution (zString b) (-alpha)) l =
        if l = qubitWeight b then (((2 : ℝ)^n * alpha : ℝ) : Real.Angle) else 0) ∧
    (∀ (k : ℕ) (V : QMat n), 1 ≤ k → k ≤ n → V ∈ u1Group n k →
      ∀ l : ℕ, k < l → l ≤ n → u1BodyPhase V l = 0) ∧
    (∀ (H V : ℝ → QMat n) (T : ℝ), Propagator H V T →
      (∀ t ∈ Set.Icc 0 T, U1Invariant (H t)) → ∀ l : ℕ, l ≤ n →
      u1BodyPhase (V T) l =
        ((-∫ t in (0 : ℝ)..T, (Matrix.trace (H t * u1Central n l)).re : ℝ) : Real.Angle)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P14

end
