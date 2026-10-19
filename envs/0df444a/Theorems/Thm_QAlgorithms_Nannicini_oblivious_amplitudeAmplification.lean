-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_oblivious_amplitudeAmplification
-- name    : QAlgorithms.Nannicini.oblivious_amplitudeAmplification
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:45:23.770369+00:00
-- url     : https://prove2.me/theorems/1dbb3292-06e0-4e1f-845c-f2a4ac44dafc
-- title:
--   Oblivious amplitude amplification: each iteration rotates by 2θ
-- statement:
--   Let $U$ be a unitary on $n+1$ qubits (first qubit = flag), $V$ a unitary on $n$ qubits and $\theta\in(0,\pi/2)$, and suppose that for every $n$-qubit state $|\psi\rangle$ there is a vector $|\phi_\psi\rangle$, which may depend on $|\psi\rangle$, with
--
--   $$U|0\rangle|\psi\rangle=\sin\theta\,|0\rangle V|\psi\rangle+\cos\theta\,|1\rangle|\phi_\psi\rangle.$$
--
--   Let $R=2|0\rangle\langle0|\otimes I^{\otimes n}-I^{\otimes(n+1)}$ and $G=-UR^\dagger U^\dagger R$. Then for every $n$-qubit state $|\psi\rangle$ and every integer $k>0$,
--
--   $$G^kU|0\rangle|\psi\rangle=\sin((2k+1)\theta)\,|0\rangle V|\psi\rangle+\cos((2k+1)\theta)\,|1\rangle|\phi_\psi\rangle.$$
--
--   Thus amplitude amplification can be performed with a single copy of $|\psi\rangle$, without a circuit that prepares it: $G$ rotates by $2\theta$ in the plane spanned by $|0\rangle V|\psi\rangle$ and $|1\rangle|\phi_\psi\rangle$.
--
--   **Formalization Note** The printed clause "where $|\psi\rangle$ may depend on $|\psi\rangle$" is a typo for $|\phi\rangle$, as in Lemma 4.11. The condition $k>0$ is kept as printed (the identity also holds at $k=0$).
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 82, Theorem 4.12. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini





/-- Nannicini p.82, Theorem 4.12 (Oblivious amplitude amplification; Lem. 3.6 of Berry et al.
2014): in the setting of Lemma 4.11 (`U`, `V` unitaries on `n + 1` and `n` qubits, flag qubit
first, `θ ∈ (0, π/2)`, and `U|0⟩|ψ⟩ = sin θ |0⟩V|ψ⟩ + cos θ |1⟩|ϕ(ψ)⟩` for every `n`-qubit state
`|ψ⟩`; the printed "where |ψ⟩ may depend on |ψ⟩" is a typo for `|ϕ⟩`), let
`R = 2|0⟩⟨0| ⊗ I^{⊗n} − I^{⊗(n+1)}` and `G = −U R† U† R`. Then for every state `|ψ⟩` and every
integer `k > 0`, `G^k U|0⟩|ψ⟩ = sin((2k+1)θ) |0⟩V|ψ⟩ + cos((2k+1)θ) |1⟩|ϕ(ψ)⟩`. -/
theorem oblivious_amplitudeAmplification {n : ℕ}
    (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) (k : ℕ) (hk : 0 < k) :
    let R : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ :=
      Matrix.kronecker (reflAt false) (1 : Matrix (Qubits n) (Qubits n) ℂ)
    let G := -(U * star R * star U * R)
    act (G ^ k) (act U (tensorVec (ket false) ψ)) =
      (Real.sin ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket false) (act V ψ) +
        (Real.cos ((2 * (k : ℝ) + 1) * θ) : ℂ) • tensorVec (ket true) (ϕ ψ) := by
  sorry

end QAlgorithms.Nannicini
