-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_theorem_1_1
-- name    : ShortestPlanarDisjoint.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:58.487734+00:00
-- url     : https://prove2.me/theorems/09c05cde-a2b4-440d-b6f6-0125a3039126
-- title:
--   Theorem 1.1 — Arbitrary terminal positions
-- statement:
--   For every finite undirected simple planar graph with k prescribed pairs of distinct terminals and arbitrary nonnegative integer edge costs at most W, one randomized finite bit program returns an optimum linkage or correctly reports infeasibility with probability at least 2/3. It receives no embedding. For absolute natural constants chosen before any input or tape, its actual execution is bounded by
--
--   $$A N^{ak+b}(W+1)^d,\qquad N=\max(2,n).$$
--
--   For every fixed polynomial weight exponent this is n^{O(k)}, with the conventional polynomial envelope for trivial cases. For every real delta in (0,1/2), a number of repetitions depending only on delta and bounded by O(log(1/delta)) achieves success at least 1−delta with the same factor in time. Every tape halts and yields feasible paths or an infeasibility flag. For each fixed k and weight exponent C, actual logspace-uniform Boolean circuit families have polynomial size and depth O(log² n), with independent fair inputs and decoded search outputs. This retains arbitrary terminal positions, disconnected and infeasible inputs, zero costs, and the adjacent fixed-k RNC² consequence.
--
--   Differences from the source:
--   - encoding: randomized search and its time, success, amplification and RNC² conventions → zero-based Fin graph/terminal labels, fixed pair orientations, a finite multitape bit program, bounded executions on every fair tape, decoded actual path outputs and logspace-generated bounded-fan-in circuits; reason: success and charged resources are conclusions; finite relabelling and fixed path orientation change no linkage or cost, and polynomial encoding/bit overhead preserves the stated asymptotic classes, including input, arithmetic, validation and output
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
--   - encoding: finite graphs, unordered prescribed pairs, optimum paths and infeasibility → Fin n vertices, one fixed orientation for each pair's actual simple walk, a tagged output and attained optimality; reason: finite relabelling and path orientation change no source instance or cost; infeasibility is distinct from an optimum of zero
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Theorem 1.1 and Section 1.1, p. 2 (PDF p. 4)

import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_ShortestPlanarDisjoint_Main_Computation

set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main

/-- Full arbitrary-position search theorem, including the standing cost and
success conventions of §1.1 and the adjacent fixed-k RNC² assertion. The same
finite sequential program works for every input and every amplification request.
No embedding, optimum, correct query, or execution-time assignment is an input. -/
theorem theorem_1_1 :
    (∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k W : ℕ) (I : RoutingInput n k),
        RobertsonSeymour1986.GM5.IsPlanar I.graph →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ I.bits)
          (A * (max 2 n) ^ (a * k + b) * (W + 1) ^ d) (2 / 3)) ∧
      (∀ (δ : ℝ), 0 < δ → δ < 1 / 2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1 / δ) / Real.log 2⌉₊) ∧
          ∀ (n k W : ℕ) (I : RoutingInput n k),
            RobertsonSeymour1986.GM5.IsPlanar I.graph →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ I.bits)
              (repetitions * A * (max 2 n) ^ (a * k + b) * (W + 1) ^ d)
              (1 - δ))) ∧
    (∀ (k C : ℕ), ∃ (F : RandomCircuitFamily) (A d : ℕ),
      LogspaceUniform F.uniform A d ∧
      (∀ n, (F.uniform.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.uniform.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n : ℕ) (I : RoutingInput n k),
        RobertsonSeymour1986.GM5.IsPlanar I.graph →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ (max 2 n) ^ C) →
        F.ExecutesSearch I I.bits (2 / 3)) := by sorry

end ShortestPlanarDisjoint.Main
