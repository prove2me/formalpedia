-- Prove2me | Theorems.Thm_QuantumLTF_Example_theorem_5_8_query
-- name    : QuantumLTF.Example.theorem_5_8_query
-- status  : Open
-- author  : @stockfish-soup
-- created : 2026-11-14T17:55:56.361937+00:00
-- url     : https://prove2.me/theorems/9a585b0a-dcc6-4ca7-b4ee-16d91ce24680
-- title:
--   Theorem 5.8 — $O(n^{1/4}/\sqrt\epsilon)$ quantum-example query bound
-- statement:
--   Let $n\ge2$, let $w\in\mathbb S^{n-1}$, and let $0<\epsilon<1/2$. For a sufficiently fine power-of-two discretization $M$, coherent access to the discretized Gaussian quantum-example oracle $\operatorname{QEX}_M(f_w,\gamma_n)$ and its inverse suffices to output a unit vector $\widetilde w$ satisfying
--
--   $$
--   \|\widetilde w-w\|\le\epsilon
--   $$
--
--   with probability at least $2/3$, using
--
--   $$
--   O\!\left(\frac{n^{1/4}}{\sqrt\epsilon}\right)
--   $$
--
--   oracle calls. The circuit is fixed before the unknown direction $w$, and the guarantee holds for every unitary extension of the prescribed example state.
--
--   This formalizes the query-complexity clause of Theorem 5.8, the paper’s quartic quantum speedup in dimension. The additional-gate and classical-postprocessing bounds are intentionally separated into later formalization targets rather than hidden in an unconstrained decoder.
--
--   **Formalization Note** The output coordinates are measured fixed-point numbers on designated wires, and the output is required to have unit norm exactly.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Theorem 5.8, pp. 72–74 (PDF pp. 73–75), query-complexity clause

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_readFp
import Definitions.Def_QuantumLTF_Example_qex

namespace QuantumLTF.Example

open QAlgorithms QuantumLTF.Membership

/-- **Theorem 5.8, query-complexity clause.** A homogeneous LTF can be learned from the paper’s finite discretized Gaussian quantum-example oracle using `O(n^(1/4)/sqrt ε)` oracle calls. -/
theorem theorem_5_8_query :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ (q m ℓo fo : ℕ)
        (c : OracleCircuit gates12 (fun _ : Fin 1 => n * q + 1) m)
        (out : Fin n → (Fin ℓo ↪ Fin m)),
        (c.queryCount 0 : ℝ) ≤ C * Real.rpow n (1 / 4) / Real.sqrt ε ∧
        ∀ w : EuclideanSpace ℝ (Fin n), ‖w‖ = 1 →
          ∀ U : Matrix (Fin (n * q + 1) → Bool) (Fin (n * q + 1) → Bool) ℂ, IsQEX w U →
            probEvent (act (c.unitary fun _ => U) (zeroKet m))
              (fun z => let wt := WithLp.toLp 2 fun i => readFp (out i) fo z
                ‖wt‖ = 1 ∧ ‖wt - w‖ ≤ ε) ≥ 2 / 3 := by sorry

end QuantumLTF.Example
