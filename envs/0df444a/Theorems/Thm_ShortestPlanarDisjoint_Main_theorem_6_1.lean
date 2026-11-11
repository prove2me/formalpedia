-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_theorem_6_1
-- name    : ShortestPlanarDisjoint.Main.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:23.151384+00:00
-- url     : https://prove2.me/theorems/e6a39601-a9a7-416f-906a-20a986c4c33a
-- title:
--   Theorem 6.1 — Euler-genus extension
-- statement:
--   For every supplied cellular embedding of Euler genus g_E and prescribed terminal pairs assigned to f used faces, one randomized finite bit program finds optimum paths or reports infeasibility within A 4^k N^{a(g_E+f)+b}(W+1)^d bit transitions. Original costs range from zero to W. The constants precede all graph, genus, face, cost and tape data. Success is at least 1−1/n and at least 2/3; logarithmic repetitions reduce error to any delta in (0,1/2). For fixed g_E,f,C and fixed c with k≤c log n and W≤N^C, actual logspace-uniform RNC² circuits perform the search. All clauses cover orientable and nonorientable surfaces, including empty terminal families.
--
--   Differences from the source:
--   - encoding: randomized search and its time, success, amplification and RNC² conventions → zero-based Fin graph/terminal labels, fixed pair orientations, a finite multitape bit program, bounded executions on every fair tape, decoded actual path outputs and logspace-generated bounded-fan-in circuits; reason: success and charged resources are conclusions; finite relabelling and fixed path orientation change no linkage or cost, and polynomial encoding/bit overhead preserves the stated asymptotic classes, including input, arithmetic, validation and output
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - encoding: the explicit success bound 1−1/n and the standing 2/3 convention → their maximum, with all-tape validation and logarithmic error amplification; reason: this keeps both source requirements, including the small-n cases, rather than weakening either
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Theorem 6.1, p. 29 (PDF p. 31)

import Definitions.Def_ShortestPlanarDisjoint_Main_Embedding
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Full surface search theorem, for both kinds of surface, with actual bit costs,
exact 4^k dependence, isolation probability, amplification and uniform RNC². -/
theorem theorem_6_1 :
    (∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k g f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ E.bits)
          (A * 4 ^ k * (max 2 n) ^ (a * (g + f) + b) * (W + 1) ^ d)
          (max (2 / 3) (1 - 1 / (n : ℝ)))) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1 / δ) / Real.log 2⌉₊) ∧
          ∀ (n k g f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
            E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ E.bits)
              (repetitions * A * 4 ^ k * (max 2 n) ^ (a * (g + f) + b) * (W + 1) ^ d)
              (1 - δ))) ∧
    (∀ (g f C c : ℕ), ∃ (F : RandomCircuitFamily) (A d : ℕ),
      LogspaceUniform F.uniform A d ∧
      (∀ n, (F.uniform.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.uniform.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n k : ℕ) (I : RoutingInput n k) (E : FaceInput I f),
        E.IsCellular → E.embedding.eulerGenus = (g : ℤ) →
        k ≤ c * logEnvelope n →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ (max 2 n) ^ C) →
        F.ExecutesSearch I E.bits (max (2 / 3) (1 - 1 / (n : ℝ)))) := by sorry
end ShortestPlanarDisjoint.Main
