-- Prove2me | Theorems.Thm_QuantumLTF_Membership_Supplement_theorem_4_10
-- name    : QuantumLTF.Membership.Supplement.theorem_4_10
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T10:46:11.551806+00:00
-- url     : https://prove2.me/theorems/05a18b89-f14f-413d-87dc-9abf607c8bc9
-- title:
--   Theorem 4.10 — time-efficient algorithm for $1\le|A|\le k$: $O(\log k)$ queries, $O(n\log n\log k)$ gates, $O(\log n\log k)$ depth
-- statement:
--   Fix any constant $\epsilon\in(0,1)$. There is a constant $C>0$ such that for every $2\le k\le n$ there is a quantum algorithm, using gates on one or two qubits with all-to-all connectivity, which, for every hidden set $A$ with $1\le|A|\le k$, outputs $A$ with error probability at most $\epsilon$ and uses
--
--   1. at most $C\log k$ oracle calls,
--   2. at most $C\,n\log n\log k$ non-oracle gates,
--   3. non-oracle depth at most $C\log n\log k$.
--
--   The paper's algorithm is obtained from the adversary solution of Eq. (144).
--
--   **Formalization Note** The algorithm is one oracle circuit chosen before $A$; controlled oracle calls are allowed.
--
--   Differences from the source:
--   - reading: the algorithm obtained from the adversary solution in Equation (144) → there is an oracle circuit over one- and two-qubit unitaries (gates12) on m wires from |0…0⟩, with plain, inverse or controlled calls to the Majority bit oracle, fixed before A; reason: the theorem asserts the complexity of an algorithm; the existence of one algorithm with these bounds is its content, and the paper's construction applies the oracle controlled on a clock register
--   - reading: has error at most ϵ → every A of the promise is output (indicator bits on designated wires) with probability at least 1 − ε; reason: error probability as in Definition 2.2
--   - reading: non-oracle depth, assuming all-to-all connectivity → nonOracleDepth: ASAP layering over the steps, gates cost 1, oracle calls 0 but order the wires they touch; reason: §C.5's circuit model
--   - encoding: fix any constant ϵ ∈ (0,1); O(log k), O(n log n log k), O(log n log k) → ∀ ε ∈ (0,1), ∃ C > 0 fixed before k and n bounding queryCount by C log k, gateCount by C n log n log k and nonOracleDepth by C log n log k; reason: the constants may depend on the fixed ε; log natural
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorem 4.10, p. 56 (PDF p. 57); §C.5, p. 95 (PDF p. 96)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_majOracle
import Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth

namespace QuantumLTF.Membership.Supplement

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 4.10 (Complexity of the algorithm for the `1 ≤ |A| ≤ k` promise).** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorem 4.10,
p. 56 (PDF p. 57): "Let `2 ≤ k ≤ n`, suppose that `1 ≤ |A| ≤ k`, and fix any constant `ϵ ∈ (0, 1)`. The algorithm
obtained from the adversary solution in Equation (144) has error at most `ϵ` and uses `O(log k)` oracle
calls, `O(n log n log k)` non-oracle gates, `O(log n log k)` non-oracle depth, assuming all-to-all
connectivity and using gates acting on one or two qubits."

**Formalization Note.** "The algorithm obtained from …" is read as the existence of such an algorithm
(an oracle circuit over one- and two-qubit unitaries, `gates12`, §C.5, on `m` wires from `|0…0⟩`, with
controlled calls to the Majority bit oracle allowed, p. 54), chosen before `A`. "Error at most `ϵ`":
every `A` of the promise is output (indicator bits on the wires `out`) with probability at least
`1 − ϵ`. The constant `C` may depend on `ϵ` ("fix any constant `ϵ`") and is fixed before `k, n`.
Oracle calls: `queryCount`; non-oracle gates: `gateCount`; non-oracle depth: `nonOracleDepth`
(queries cost `0`). `log` is natural; `n ≥ k ≥ 2`, so all logarithms are positive. -/
theorem theorem_4_10 :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ k n : ℕ, 2 ≤ k → k ≤ n → 
        ∃ (m : ℕ) (c : OracleCircuit gates12 (fun _ : Fin 1 => n + 1) m) (out : Fin n ↪ Fin m),
          (c.queryCount 0 : ℝ) ≤ C * Real.log k ∧
          (c.gateCount : ℝ) ≤ C * n * Real.log n * Real.log k ∧
          (nonOracleDepth c : ℝ) ≤ C * Real.log n * Real.log k ∧
          ∀ A : Finset (Fin n), 1 ≤ A.card ∧ A.card ≤ k →
            open Classical in
            probEvent (act (c.unitary fun _ => majOracle A) (zeroKet m))
              (fun z => ∀ i : Fin n, z (out i) = decide (i ∈ A)) ≥ 1 - ε := by sorry

end QuantumLTF.Membership.Supplement
