-- Prove2me | Theorems.Thm_QAlgorithms_Childs_compressedPhaseOracle_containsZero_le
-- name    : QAlgorithms.Childs.compressedPhaseOracle_containsZero_le
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:35:10.469987+00:00
-- url     : https://prove2.me/theorems/62fc6344-5759-46bd-9ea5-b04fb991dbe6
-- title:
--   One compressed phase query raises ‖P ψ‖ by at most √(2/2^m)
-- statement:
--   Let $n,m\ge0$, $\Sigma=\{0,1\}^m$, and let $W$ be a finite workspace. Consider the Hilbert space with computational basis $|x,z,w,y\rangle$, where $x\in[n]$ is the query input, $z\in\Sigma$ the query output, $w\in W$ the workspace and $y\in(\Sigma\cup\{\perp\})^n$ the oracle register. The compressed phase oracle is
--
--   $$
--   \Phi=(I\otimes H^{\otimes m}\otimes I\otimes C^{\otimes n})\,\Lambda\,(I\otimes H^{\otimes m}\otimes I\otimes C^{\otimes n}).
--   $$
--
--   Here $H$ is the Hadamard gate, $C$ is the compression unitary of §26.1 (it swaps $|\perp\rangle$ and $|\hat 0\rangle$ and fixes $|\hat y\rangle$ for $y\ne0$), and $\Lambda|x,z,w,y\rangle=|x,z\oplus y_x,w,y\rangle$ (the identity when $y_x=\perp$). Let $P$ be the projection onto the basis states whose oracle register contains a zero, i.e. $y_{x^*}=0^m$ for some $x^*$. Then for every state $|\psi\rangle$ (unit vector),
--
--   $$
--   \|P\,\Phi|\psi\rangle\|\;\le\;\|P|\psi\rangle\|+\sqrt{\frac{2}{2^m}} .
--   $$
--
--   Iterated over $t$ queries, this shows that the compressed-oracle probability of having recorded a zero is $O(t^2/2^m)$. Combined with Lemma 26.1, this gives the $\Omega(2^{m/2})$ query lower bound for unstructured search against a random oracle.
--
--   **Formalization Note** $|\psi\rangle$ is an arbitrary unit vector of the full space; no reachability condition is imposed, and the proof uses none. The register order is $((x,z),w),y$, as in (26.30).
-- source:
--   Andrew Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF p. 136, Fact 26.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_CompressedOracle
set_option autoImplicit false

namespace QAlgorithms.Childs


/-- Childs, Fact 26.2 (PDF p. 136): for every state `|ψ⟩` of the registers
`|x, z, w, y⟩` (input `x ∈ [n]`, output `z ∈ Σ`, workspace `w`, oracle register
`y ∈ (Σ ∪ {⊥})^n`, (26.30)), one application of the compressed phase oracle `Φ` (26.29) raises
the norm of the projection `P` onto basis states whose oracle register contains a zero by at
most `√(2 / 2^m)`: `‖P Φ |ψ⟩‖ ≤ ‖P |ψ⟩‖ + √(2/2^m)`. -/
theorem compressedPhaseOracle_containsZero_le {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (ψ : EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))))
    (hψ : IsState ψ) :
    ‖act (containsZeroProj n m W) (act (compressedPhaseOracle n m W) ψ)‖ ≤
      ‖act (containsZeroProj n m W) ψ‖ + Real.sqrt (2 / 2 ^ m) := by
  sorry

end QAlgorithms.Childs
