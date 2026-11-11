-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_theorem_1_2
-- name    : ShortestPlanarDisjoint.Main.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:40.989386+00:00
-- url     : https://prove2.me/theorems/373c2378-f888-49b0-8022-91c04de0599f
-- title:
--   Theorem 1.2 — Terminals on few faces
-- statement:
--   Shortest disjoint paths with k prescribed pairs on f used specified faces of a planar graph can be solved by one randomized finite program in A 4^k N^{a f+b}(W+1)^d time. With a supplied cellular embedding of Euler genus g_E, the envelope is A 4^k N^{a(g_E+f)+b}(W+1)^d. Original costs may be zero. Both programs return actual optimum paths or correct infeasibility with probability at least 2/3, and achieve error delta with an O(log(1/delta)) repetition factor. These bounds give exactly 4^k n^{O(f)} and 4^k n^{O(g_E+f)} for every fixed polynomial weight exponent. For fixed genus, face count, weight exponent and logarithmic coefficient with k=O(log n), search is in logspace-uniform RNC². The planar case has g_E=0 and permits disconnected graphs.
--
--   Differences from the source:
--   - encoding: randomized search and its time, success, amplification and RNC² conventions → zero-based Fin graph/terminal labels, fixed pair orientations, a finite multitape bit program, bounded executions on every fair tape, decoded actual path outputs and logspace-generated bounded-fan-in circuits; reason: success and charged resources are conclusions; finite relabelling and fixed path orientation change no linkage or cost, and polynomial encoding/bit overhead preserves the stated asymptotic classes, including input, arithmetic, validation and output
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - generalization: used faces of one supplied planar embedding → componentwise planar rotations with face labels consistent within each component, also allowing other groupings across components; reason: every source embedding induces such data; processing components separately proves the same bound for all these groupings, since each component uses at most f face labels and total pair count is k
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Theorem 1.2, p. 2 (PDF p. 4)

import Definitions.Def_ShortestPlanarDisjoint_Main_Embedding
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Planar and cellular-surface bounds, including all weight, amplification and
parallel clauses. A planar input may be disconnected. -/
theorem theorem_1_2 :
    (∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        E.embedding.IsPlanar →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ E.bits)
          (A * 4 ^ k * (max 2 n) ^ (a * f + b) * (W + 1) ^ d) (2 / 3)) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1 / δ) / Real.log 2⌉₊) ∧
          ∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
            E.embedding.IsPlanar →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ E.bits)
              (repetitions * A * 4 ^ k * (max 2 n) ^ (a * f + b) * (W + 1) ^ d)
              (1 - δ))) ∧
    (∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k g f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ E.bits)
          (A * 4 ^ k * (max 2 n) ^ (a * (g + f) + b) * (W + 1) ^ d) (2 / 3)) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1/2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1/δ) / Real.log 2⌉₊) ∧
          ∀ (n k g f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
            E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ E.bits)
              (repetitions * A * 4 ^ k * (max 2 n) ^ (a * (g + f) + b) * (W + 1) ^ d)
              (1-δ))) ∧
    (∀ (g f C c : ℕ), ∃ (F : RandomCircuitFamily) (A d : ℕ),
      LogspaceUniform F.uniform A d ∧
      (∀ n, (F.uniform.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.uniform.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n k : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        ((g = 0 ∧ E.embedding.IsPlanar) ∨
          (E.IsCellular ∧ E.embedding.eulerGenus = (g : ℤ))) →
        k ≤ c * logEnvelope n →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ (max 2 n) ^ C) →
        F.ExecutesSearch I E.bits (2 / 3)) := by sorry
end ShortestPlanarDisjoint.Main
