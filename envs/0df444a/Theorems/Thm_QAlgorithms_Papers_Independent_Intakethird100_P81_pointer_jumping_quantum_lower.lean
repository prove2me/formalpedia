-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P81_pointer_jumping_quantum_lower
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P81.pointer_jumping_quantum_lower
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:55:36.863204+00:00
-- url     : https://prove2.me/theorems/1c88deff-2f37-42c3-af67-ed0337249599
-- title:
--   Quantum pointer-parity round lower bound
-- statement:
--   Let $f_k$ be pointer parity on two separately owned, unrestricted maps between two disjoint sets of $n$ labelled vertices. Starting from a fixed vertex $v_1$ on Alice's side, follow $k+1$ alternating pointers and XOR all bits of the endpoint's standard binary label. A protocol has $k\ge1$ alternating messages, Bob starts, and the final local output announcement is uncharged. Its cost $c$ counts transmitted qubits; its finite workspace and normalized prior entangled state are independent of both inputs. Correctness with probability at least $2/3$ is required for every pair of maps.
--
--   There are absolute constants $C>0$ and $n_0\ge2$, chosen before $k,n,v_1$ and the protocol, such that for every $n\ge n_0$,
--   $$
--   c\ge \frac{n}{2^{2^{Ck}}}-k\log_2 n.
--   $$
--
--   This retains the displayed double exponential and subtractive logarithmic term. It compares the cost of every admissible protocol, including protocols with arbitrary finite prior entanglement.
-- source:
--   On rounds in quantum communication, arXiv:quant-ph/0004100v5, PDF p. 14, Theorem 3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P81

noncomputable section

open scoped Matrix ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intakethird100.P81

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)

open QAlgorithms.Papers.Independent.Bridge50.P44 (ClassicalFirst)

/-- Theorem 3, PDF p.14 (announcement p.3): universal double-exponential dependence on k.
The displayed binary log is retained; integer pointer-message overhead is absorbed in C. -/
theorem pointer_jumping_quantum_lower :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ (k n : ℕ), 0 < k → n0 ≤ n → ∀ v1 : Fin n,
      ∀ P : QuantumProtocol (PointerMap n) (PointerMap n) Bool,
        P.valid .bob k → P.computes (pointerParity k v1) (1 / 3) →
        (n : ℝ) / (2 : ℝ) ^ ((2 : ℝ) ^ (C * k)) - k * Real.logb 2 n ≤ P.cost := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P81

end
