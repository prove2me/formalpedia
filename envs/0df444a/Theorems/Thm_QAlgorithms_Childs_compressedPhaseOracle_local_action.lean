-- Prove2me | Theorems.Thm_QAlgorithms_Childs_compressedPhaseOracle_local_action
-- name    : QAlgorithms.Childs.compressedPhaseOracle_local_action
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T16:45:09.569629+00:00
-- url     : https://prove2.me/theorems/b6fafe89-f7b8-4ec6-95a7-8f7cda713416
-- title:
--   Compressed phase queries act on the queried oracle register only
-- statement:
--   Fix the query input $x$, the Fourier-basis query output $z$, and a workspace basis label $w$. Let $C$ be the compression unitary on one oracle cell, and let $D_z$ be diagonal with value $1$ at $\bot$ and value $(-1)^{z\cdot v}$ at a stored bit string $v$.
--
--   The full compressed phase oracle leaves $x,z,w$ and every oracle cell other than $x$ unchanged, and applies $C D_z C$ to cell $x$. More precisely, for every vector $\psi$ and every oracle configuration $y$,
--   $$
--   (\Phi\psi)(x,z,w,y)=\sum_{o\in\Sigma\cup\{\bot\}}(C D_z C)_{y_x,o}\,\psi(x,z,w,y[x\leftarrow o]).
--   $$
--   No normalization assumption on $\psi$ is needed. This is the local form of equation (26.29), used in the calculations (26.33)–(26.39) for Fact 26.2. It isolates cancellation of the unqueried compression factors and Fourier diagonalization of the lookup operation.
-- source:
--   Andrew M. Childs, Lecture Notes on Quantum Algorithms, 17 April 2025, PDF pp.135–136 (printed pp.128–129), equation (26.29) and local-action calculations (26.33)–(26.39) in the proof of Fact 26.2. https://www.cs.umd.edu/~amchilds/qa/qa.pdf

import Definitions.Def_QAlgorithms_Defs_CompressedOracle

namespace QAlgorithms.Childs

theorem compressedPhaseOracle_local_action {n m : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (ψ : EuclideanSpace ℂ (((Fin n × Qubits m) × W) × (Fin n → Option (Qubits m))))
    (a : (Fin n × Qubits m) × W) (y : Fin n → Option (Qubits m)) :
    act (compressedPhaseOracle n m W) ψ (a, y) =
      ∑ o : Option (Qubits m),
        (compressionUnitary m * Matrix.diagonal (fun t : Option (Qubits m) =>
          match t with
          | none => (1 : ℂ)
          | some v => if dotBits a.1.2 v then -1 else 1) * compressionUnitary m)
            (y a.1.1) o * ψ (a, Function.update y a.1.1 o) := by sorry

end QAlgorithms.Childs
