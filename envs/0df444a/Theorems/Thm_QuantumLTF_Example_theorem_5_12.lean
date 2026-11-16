-- Prove2me | Theorems.Thm_QuantumLTF_Example_theorem_5_12
-- name    : QuantumLTF.Example.theorem_5_12
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-15T20:35:38.169083+00:00
-- url     : https://prove2.me/theorems/a316c835-71c4-4a14-9e48-946f495975b3
-- title:
--   Theorem 5.12 — quantum example-oracle lower bound
-- statement:
--   For every $n\ge2$ and $0<\epsilon\le1/(8\pi)$, any quantum learner which outputs, with probability at least $2/3$, a measurable classifier of Gaussian disagreement at most $\epsilon$ from every homogeneous LTF requires $\Omega(n^{1/4}/\sqrt\epsilon)$ calls to the quantum-example oracle or its inverse. The learner may be adaptive and improper.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, STOC 2027 submission #347, Theorem 5.12, p. 77 (PDF p. 78); also Theorem 1.4.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Example_qex

namespace QuantumLTF.Example

open QAlgorithms QuantumLTF.Membership

theorem theorem_5_12 :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (8 * Real.pi) →
      ∀ q m (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) m)
        (decode : Qubits m → (EuclideanSpace ℝ (Fin n) → ℤ)),
        (∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 → ∀ U, IsQEX w U →
          probEvent (act (c.unitary fun _ => U) (zeroKet m))
            (fun z => disagree (decode z) (ltf w 0) ≤ ε) ≥ 2 / 3) →
        C * n ^ (1 / 4 : ℝ) / Real.sqrt ε ≤ c.queryCount 0 := by sorry

end QuantumLTF.Example
