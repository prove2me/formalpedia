-- Prove2me | Theorems.Thm_ShortestPlanarDisjoint_Main_theorem_5_10
-- name    : ShortestPlanarDisjoint.Main.theorem_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:40:49.538019+00:00
-- url     : https://prove2.me/theorems/d951be07-43c2-425e-95e5-ebb0d391e641
-- title:
--   Theorem 5.10 — Pairing based refinement
-- statement:
--   Let the connected nontrivial planar input have f used terminal faces, chosen terminal-free gaps and an arbitrary activity vector a. In every inactive block, the prescribed pairing has no consecutive pair in its linear, nonwrapping terminal order. Put tau equal to the total number of terminals in active blocks. One randomized bit program returns an optimum linkage or reports infeasibility in time 2^tau N^{a_0 f+b_0} poly(W+1), with uniform constants and success at least max(2/3,1−1/n). Error delta is attained with O(log(1/delta)) repetitions. There is no restriction on k. For fixed f, weight exponent C and coefficient c in tau≤c log n, search is in logspace-uniform RNC², still with arbitrary k.
--
--   Differences from the source:
--   - encoding: randomized search and its time, success, amplification and RNC² conventions → zero-based Fin graph/terminal labels, fixed pair orientations, a finite multitape bit program, bounded executions on every fair tape, decoded actual path outputs and logspace-generated bounded-fan-in circuits; reason: success and charged resources are conclusions; finite relabelling and fixed path orientation change no linkage or cost, and polynomial encoding/bit overhead preserves the stated asymptotic classes, including input, arithmetic, validation and output
--   - encoding: uniform O bounds with fixed weight exponent and fixed logarithmic coefficient → uniform natural coefficients and exponents before instance data, N=max(2,n), k≤c ceil(log₂ N), and ceil(log₂(1/δ)) repetition envelopes; reason: natural exponents cover every fixed real exponent by rounding up; small cases have finite envelopes; no witness depends on a graph, optimum or random tape
--   - encoding: a supplied cellular embedding with corner assignments on a connected surface → a Fin-indexed signed rotation flag map with computed integer Euler genus, explicit corners and used-face labels; reason: this is the same finite cellular embedding up to barycentric realization, including both orientable and nonorientable cases; connectedness is necessary for cellularity, and isolated single-vertex spheres are retained
--   - encoding: the Section 5.1 gaps and linear terminal blocks, with M in M_a → finite gap choices and explicit facial boundary walks, with no consecutive prescribed pair in every substituted block; reason: the walk preserves corner occurrences and the excluded wrapping gap; reversing a block order preserves the same consecutive-pair condition, and tau counts all active terminals
--   - encoding: high probability and the Section 1.1 cost/amplification conventions → success max(2/3,1−1/n), an arbitrary-cost polynomial factor and uniform logarithmic amplification; reason: this is the Section 4 isolation/repetition reading required by the brief; it preserves 2^tau exactly and includes polynomially bounded costs
-- source:
--   Srijan Chakraborty, Anish Mukherjee, STOC 2027 submission #1387 (October 2026), Theorem 5.10, p. 28 (PDF p. 30)

import Definitions.Def_ShortestPlanarDisjoint_Main_Seams
set_option autoImplicit false

namespace ShortestPlanarDisjoint.Main
/-- Full pairing-based refinement for every permitted activity vector. The input
includes gap choices determining linear, nonwrapping block orders; it includes
neither seams nor a correct coefficient oracle. k has no logarithmic restriction. -/
theorem theorem_5_10 :
    (∃ (P : BitProgram) (A a b d : ℕ), 0 < A ∧
      (∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f)
          (gaps : E.GapChoice) (active : Fin f → Bool),
        0 < k → E.IsCellular → E.embedding.IsPlanar →
        E.AllowedPairing (E.blockOrder gaps) active →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
        ExecutesSearch P I (numberBits 1 ++ E.bits ++ gaps.bits ++ List.ofFn active)
          (A * 2 ^ (E.tau active) * (max 2 n) ^ (a * f + b) * (W+1) ^ d)
          (max (2/3) (1 - 1/(n : ℝ)))) ∧
      (∀ δ : ℝ, 0 < δ → δ < 1/2 →
        ∃ repetitions : ℕ, 0 < repetitions ∧
          repetitions ≤ A * (1 + ⌈Real.log (1/δ) / Real.log 2⌉₊) ∧
          ∀ (n k f W : ℕ) (I : RoutingInput n k) (E : FaceInput I f)
              (gaps : E.GapChoice) (active : Fin f → Bool),
            0 < k → E.IsCellular → E.embedding.IsPlanar →
            E.AllowedPairing (E.blockOrder gaps) active →
            (∀ e ∈ I.graph.edgeSet, I.weight e ≤ W) →
            ExecutesSearch P I (numberBits repetitions ++ E.bits ++ gaps.bits ++ List.ofFn active)
              (repetitions * A * 2 ^ (E.tau active) * (max 2 n) ^ (a * f + b) * (W+1) ^ d)
              (1-δ))) ∧
    (∀ (f C c : ℕ), ∃ (F : RandomCircuitFamily) (A d : ℕ),
      LogspaceUniform F.uniform A d ∧
      (∀ n, (F.uniform.circuit n).size ≤ A * (max 2 n) ^ d ∧
        (F.uniform.circuit n).depth ≤ A * (logEnvelope n) ^ 2) ∧
      ∀ (n k : ℕ) (I : RoutingInput n k) (E : FaceInput I f)
          (gaps : E.GapChoice) (active : Fin f → Bool),
        0 < k → E.IsCellular → E.embedding.IsPlanar →
        E.AllowedPairing (E.blockOrder gaps) active →
        E.tau active ≤ c * logEnvelope n →
        (∀ e ∈ I.graph.edgeSet, I.weight e ≤ (max 2 n) ^ C) →
        F.ExecutesSearch I (E.bits ++ gaps.bits ++ List.ofFn active)
          (max (2/3) (1 - 1/(n : ℝ)))) := by sorry
end ShortestPlanarDisjoint.Main
