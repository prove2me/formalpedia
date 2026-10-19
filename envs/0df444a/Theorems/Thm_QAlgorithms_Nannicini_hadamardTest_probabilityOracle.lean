-- Prove2me | Theorems.Thm_QAlgorithms_Nannicini_hadamardTest_probabilityOracle
-- name    : QAlgorithms.Nannicini.hadamardTest_probabilityOracle
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:46:13.545817+00:00
-- url     : https://prove2.me/theorems/4bf109f9-6ca0-4713-bfff-031ef6c72a31
-- title:
--   A Hadamard-test circuit is a probability oracle for (1 + Re⟨ψ|ϕ_x⟩)/2
-- statement:
--   This is the Hadamard-test construction of a probability oracle for an inner product.
--
--   Let $U$ be a unitary on $n$ qubits with $U|0\rangle = |\psi\rangle$. Let $X$ be a finite set indexing the basis states $|x\rangle$ of an input register, and let $V$ be a unitary on the $n$-qubit register together with the input register, such that $V|0\rangle|x\rangle = |\phi_x\rangle|x\rangle$ for every $x \in X$. Consider the circuit $W$ of Fig. 5.3. It acts on a flag qubit, the $n$-qubit register and the input register, and applies in order $H$ and $X$ to the flag, controlled-$U$, $X$ to the flag, controlled-$V$, and $H$ and $X$ to the flag. Then $W$ is a probability oracle (Definition 5.9) for
--
--   $$
--   f(x) = \tfrac12\big(1 + \operatorname{Re}\langle\psi|\phi_x\rangle\big).
--   $$
--
--   That is, $W$ is unitary, $0 \le f(x) \le 1$, and for every $x$ there are quantum states $|\psi^{(0)}_x\rangle, |\psi^{(1)}_x\rangle$ with
--
--   $$
--   W|0\rangle|0\rangle|x\rangle = \sqrt{f(x)}\,|1\rangle|\psi^{(1)}_x\rangle + \sqrt{1-f(x)}\,|0\rangle|\psi^{(0)}_x\rangle.
--   $$
--
--   The circuit uses one controlled-$U$, one controlled-$V$ and five single-qubit gates. It is the input-model bridge from state-preparation unitaries to the gradient algorithm, and it underlies the tomography algorithm of §5.1.3.
--
--   **Formalization Note** The circuit is the fixed definition `hadamardTestCircuit U V`, so the resource count is part of its definition. $\langle\psi|\phi_x\rangle$ is Mathlib's inner product, which is conjugate-linear in its first argument.
-- source:
--   Giacomo Nannicini, Quantum algorithms for optimizers, 2025, v5; notes dated 9 July 2025, PDF p. 115, Proposition 5.16. https://arxiv.org/pdf/2408.07086v5

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QAlgorithms_Nannicini_Ch05a_Model
set_option autoImplicit false

namespace QAlgorithms.Nannicini



/-- Nannicini p.115, Proposition 5.16 (Hadamard-test probability oracle). Let `U` be a unitary on
`n` qubits with `U|0⟩ = |ψ⟩`, and `V` a unitary on the `n`-qubit register together with an input
register `|x⟩` (basis `X`) with `V|0⟩|x⟩ = |ϕ_x⟩|x⟩` for every `x`. Then the circuit of Fig. 5.3
(on the flag qubit: `H`, `X`, controlled-`U`, `X`, controlled-`V`, `H`, `X`) is a probability oracle
(Def. 5.9) for `f(x) = (1 + Re⟨ψ|ϕ_x⟩)/2`. Its single application of controlled-`U` and of
controlled-`V` and its five single-qubit gates are structural in `hadamardTestCircuit`. -/
theorem hadamardTest_probabilityOracle {n : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (U : Matrix (Qubits n) (Qubits n) ℂ) (V : Matrix (Qubits n × X) (Qubits n × X) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Qubits n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Qubits n × X) ℂ)
    (ϕ : X → EuclideanSpace ℂ (Qubits n))
    (hϕ : ∀ x, act V (ket ((0 : Qubits n), x)) = tensorVec (ϕ x) (ket x)) :
    IsProbabilityOracle (0 : Qubits n) (hadamardTestCircuit U V)
      (fun x => (1 + (inner ℂ (act U (zeroKet n)) (ϕ x)).re) / 2) := by
  sorry





end QAlgorithms.Nannicini
