-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_groverOperator_eigenstates
-- name    : QAlgorithms.Nannicini.groverOperator_eigenstates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:45:25.190282+00:00
-- url     : https://prove2.me/theorems/a62d2fff-d2a8-453d-ad0b-3b8c0fe3769d
-- title:
--   Eigenstates of the Grover operator in amplitude estimation
-- statement:
--   This is the spectral fact behind amplitude estimation.
--
--   Let $S$ be a unitary on $n$ qubits and let $|\psi_G\rangle, |\psi_B\rangle$ be orthogonal unit vectors such that
--   $$S|\vec 0\rangle_n = \sin\theta\,|\psi_G\rangle + \cos\theta\,|\psi_B\rangle, \qquad \theta \in [0, \tfrac{\pi}{2}].$$
--   Let $R$ be a unitary with $R|\psi_G\rangle = -|\psi_G\rangle$ and $R|\psi_B\rangle = |\psi_B\rangle$, let $F = 2|\vec 0\rangle\langle\vec 0| - I$, and let $G = S F S^\dagger R$ be the Grover operator. Define
--   $$|\phi_\pm\rangle = \frac{1}{\sqrt 2}\bigl(|\psi_G\rangle \pm i\,|\psi_B\rangle\bigr).$$
--   Then $|\phi_+\rangle$ and $|\phi_-\rangle$ are orthogonal quantum states and
--   $$G|\phi_+\rangle = e^{2i\theta}|\phi_+\rangle, \qquad G|\phi_-\rangle = e^{-2i\theta}|\phi_-\rangle.$$
--
--   Since $S|\vec 0\rangle$ is an equal-weight combination of $|\phi_+\rangle$ and $|\phi_-\rangle$, phase estimation of $G$ on $S|\vec 0\rangle$ reveals $\pm\theta/\pi$, which is how amplitude estimation recovers $\theta$.
--
--   **Formalization Note** Being an eigenstate is stated as unit norm plus the eigenvalue equation; orthogonality is the vanishing of the inner product. $F$ is `reflAt 0` and $G$ is the frozen `ampAmpIterate S R 0`.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 84, Proposition 4.15. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini

/-- Nannicini p.84, Proposition 4.15: in the setting of §4.3 (p.83: `S` an `n`-qubit unitary,
`S|0⟩ = sin θ |ψ_G⟩ + cos θ |ψ_B⟩` with `ψ_G`, `ψ_B` orthogonal states and `θ ∈ [0, π/2]`; `R` a
unitary with `R|ψ_G⟩ = −|ψ_G⟩`, `R|ψ_B⟩ = |ψ_B⟩`; `F = 2|0⟩⟨0| − I`), the states
`|ϕ±⟩ = (1/√2)(|ψ_G⟩ ± i|ψ_B⟩)` are orthogonal eigenstates of `S F S† R` with eigenvalues
`e^{2iθ}` and `e^{−2iθ}` respectively. -/
theorem groverOperator_eigenstates {n : ℕ} (S R : Matrix (Qubits n) (Qubits n) ℂ)
    (psiG psiB : EuclideanSpace ℂ (Qubits n)) (θ : ℝ)
    (hS : S ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hR : R ∈ Matrix.unitaryGroup (Qubits n) ℂ)
    (hG : IsState psiG) (hB : IsState psiB) (horth : inner ℂ psiG psiB = 0)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (hprep : act S (zeroKet n) = (Real.sin θ : ℂ) • psiG + (Real.cos θ : ℂ) • psiB)
    (hRG : act R psiG = -psiG) (hRB : act R psiB = psiB) :
    let phiPlus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG + Complex.I • psiB)
    let phiMinus := ((Real.sqrt 2)⁻¹ : ℂ) • (psiG - Complex.I • psiB)
    IsState phiPlus ∧ IsState phiMinus ∧ inner ℂ phiPlus phiMinus = 0 ∧
      act (ampAmpIterate S R 0) phiPlus = Complex.exp (2 * Complex.I * θ) • phiPlus ∧
      act (ampAmpIterate S R 0) phiMinus = Complex.exp (-(2 * Complex.I * θ)) • phiMinus := by
  sorry




end QAlgorithms.Nannicini
