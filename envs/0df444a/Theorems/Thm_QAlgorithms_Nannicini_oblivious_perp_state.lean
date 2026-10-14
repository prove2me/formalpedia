-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_oblivious_perp_state
-- name    : QAlgorithms.Nannicini.oblivious_perp_state
-- status  : Open
-- author  : @Goku
-- created : 2026-10-13T17:44:44.740867+00:00
-- url     : https://prove2.me/theorems/26d09b70-fc84-4f58-ba3d-dbbad37e4e7e
-- title:
--   Oblivious amplitude amplification: the partner state Ψ⊥ is orthogonal to |0⟩|ψ⟩ and has no flag-0 support
-- statement:
--   Let $U$ be a unitary on $n+1$ qubits, whose first qubit is a flag qubit, let $V$ be a unitary on $n$ qubits, and let $\theta\in(0,\pi/2)$. Suppose that for every $n$-qubit state $|\psi\rangle$ (unit vector) there is an $n$-qubit vector $|\phi_\psi\rangle$, which may depend on $|\psi\rangle$, with
--
--   $$U|0\rangle|\psi\rangle=\sin\theta\,|0\rangle V|\psi\rangle+\cos\theta\,|1\rangle|\phi_\psi\rangle.$$
--
--   Then for every $n$-qubit state $|\psi\rangle$ the vector
--
--   $$|\Psi^\perp\rangle=U^\dagger\bigl(\cos\theta\,|0\rangle V|\psi\rangle-\sin\theta\,|1\rangle|\phi_\psi\rangle\bigr)$$
--
--   satisfies:
--
--   1. $\langle\Psi|\Psi^\perp\rangle=0$, where $|\Psi\rangle=|0\rangle|\psi\rangle$;
--   2. $(|0\rangle\langle 0|\otimes I^{\otimes n})|\Psi^\perp\rangle=0$, i.e. $|\Psi^\perp\rangle$ has no support on basis states whose first qubit is $0$.
--
--   This lemma identifies the two-dimensional invariant subspace in which oblivious amplitude amplification rotates.
--
--   **Formalization Note** The map $\psi\mapsto\phi_\psi$ is a function argument; the hypothesis is required for every state, as the proof uses it. That $|\phi_\psi\rangle$ is a unit vector follows from the hypothesis and unitarity of $U$ and is not assumed. The $(n+1)$-qubit register is indexed by pairs (flag bit, $n$-bit string), flag first.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 81, Lemma 4.11. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_AmplitudeEstimation
set_option autoImplicit false

namespace QAlgorithms.Nannicini




/-- Nannicini p.81, Lemma 4.11 (based on Lem. 3.7 of Berry et al. 2014): let `U`, `V` be
unitaries on `n + 1` and `n` qubits (the first qubit of `U`'s register is the flag) and
`θ ∈ (0, π/2)`. Suppose that for every `n`-qubit state `|ψ⟩`,
`U|0⟩|ψ⟩ = sin θ |0⟩V|ψ⟩ + cos θ |1⟩|ϕ(ψ)⟩`. Then for every state `|ψ⟩` the state
`|Ψ⊥⟩ = U†(cos θ |0⟩V|ψ⟩ − sin θ |1⟩|ϕ(ψ)⟩)` is orthogonal to `|Ψ⟩ = |0⟩|ψ⟩` and satisfies
`(|0⟩⟨0| ⊗ I^{⊗n})|Ψ⊥⟩ = 0`. -/
theorem oblivious_perp_state {n : ℕ} (U : Matrix (Bool × Qubits n) (Bool × Qubits n) ℂ)
    (V : Matrix (Qubits n) (Qubits n) ℂ) (θ : ℝ)
    (ϕ : EuclideanSpace ℂ (Qubits n) → EuclideanSpace ℂ (Qubits n))
    (hU : U ∈ Matrix.unitaryGroup (Bool × Qubits n) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hact : ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
      act U (tensorVec (ket false) ψ) =
        (Real.sin θ : ℂ) • tensorVec (ket false) (act V ψ) +
          (Real.cos θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    (ψ : EuclideanSpace ℂ (Qubits n)) (hψ : IsState ψ) :
    let Ψperp := act (star U) ((Real.cos θ : ℂ) • tensorVec (ket false) (act V ψ) -
      (Real.sin θ : ℂ) • tensorVec (ket true) (ϕ ψ))
    inner ℂ (tensorVec (ket false) ψ) Ψperp = 0 ∧
      act (Matrix.kronecker (Matrix.diagonal fun b : Bool => if b then (0 : ℂ) else 1)
        (1 : Matrix (Qubits n) (Qubits n) ℂ)) Ψperp = 0 := by
  sorry


end QAlgorithms.Nannicini
