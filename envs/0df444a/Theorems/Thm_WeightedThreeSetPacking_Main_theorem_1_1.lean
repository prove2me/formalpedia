-- Prove2me | Theorems.Thm_WeightedThreeSetPacking_Main_theorem_1_1
-- name    : WeightedThreeSetPacking.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:41.65068+00:00
-- url     : https://prove2.me/theorems/d460d2dd-9c54-4e1b-8772-57389325ee3d
-- title:
--   Theorem 1.1 — deterministic polynomial-time 1.6908-approximation (Tong and Xu, arXiv:2610.10036v1, p. 3)
-- statement:
--   There is one deterministic algorithm and one polynomial time bound, fixed independently of the input, for every finite family of nonempty sets of size at most three with arbitrary positive rational weights. On each input it returns a feasible packing $A^+$ such that, for every optimum packing $O$,
--
--   $$w(O)\le\frac{4227}{2500}w(A^+)=1.6908w(A^+).$$
--
--   Running time is measured in the binary lengths of ground labels and rational numerators and denominators. The empty family is included. No optimum, center assignment, covering graph, local optimality certificate or approximation guarantee is an input. Algorithm 2 of Tong and Xu, arXiv:2610.10036v1, pp. 25–26 supplies the intended witness; its uniform machine implementation and correctness remain theorem proof obligations.
--
--   This is the full algorithmic guarantee, including original-weight feasibility, the exact source constant and polynomial bit complexity.
--
--   Differences from the source:
--   - encoding: A finite family of nonempty sets of size at most three, with arbitrary positive rational weights. → Duplicate-free lists of finite natural-label sets with unbounded positive numerator and denominator, and self-delimiting Boolean encodings of input and output.; reason: Finite source ground unions admit lossless relabeling; every positive rational has such a representation, and labels and integer magnitudes are unbounded.
--   - encoding: One deterministic polynomial-time algorithm returns a feasible packing with approximation ratio 1.6908. → One function and a Mathlib TM2 polynomial-time machine witness, quantified before all inputs, with feasibility and the exact rational 4227/2500 bound in the conclusion.; reason: The machine includes a single polynomial bound in binary input length; the source algorithm and its polynomial are proof witnesses, not input assumptions.
-- source:
--   Tong and Xu, arXiv:2610.10036v1, Theorem 1.1, p. 3; Algorithm 2 and §4.3, pp. 25–26; https://arxiv.org/abs/2610.10036v1

import Definitions.Def_WeightedThreeSetPacking_Main_Input

namespace WeightedThreeSetPacking.Main

open scoped BigOperators

/-- Tong and Xu, arXiv:2610.10036v1, Theorem 1.1, p. 3. -/
theorem theorem_1_1 :
    ∃ algorithm : Input → List (List ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodeOutput algorithm) ∧
      ∀ I : Input,
        Feasible I (outputFamily (algorithm I)) ∧
        ∀ O, Optimal I O →
          totalWeight I O ≤ (4227/2500 : ℝ) * totalWeight I (outputFamily (algorithm I)) := by sorry

end WeightedThreeSetPacking.Main
