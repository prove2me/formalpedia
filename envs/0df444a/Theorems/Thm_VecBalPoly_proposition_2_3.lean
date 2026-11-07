-- Prove2me | Theorems.Thm_VecBalPoly_proposition_2_3
-- name    : VecBalPoly.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:19:40.139912+00:00
-- url     : https://prove2.me/theorems/d5740f9c-9b39-488f-ac99-743f0407029e
-- title:
--   Proposition 2.3 — Algorithm 2.2 with $O((mn^9+n^{10})\log(2+m+n))$ real operations
-- statement:
--   There is a deterministic real-RAM program implementing Algorithm 2.2 that, on every input $m,n\ge1$ and $A\in\mathbb R^{m\times n}$ with columns of Euclidean norm at most $1$, halts after
--   $$O\big((mn^9+n^{10})\log(2+m+n)\big)$$
--   additions, subtractions, multiplications, divisions and comparisons of real numbers, and outputs a signing produced by Algorithm 2.2.
--
--   Combined with Proposition 5.1 and Lemma 3.1 this yields the running time part of Theorem 1.1.
--
--   **Formalization Note** "Output of Algorithm 2.2" means the rounding of the last state of a complete run whose directions meet the conclusion of Lemma 2.1 (or all $+1$ when $n\le K$).
--
--   Differences from the source:
--   - reading: "a deterministic procedure" / "can be implemented" in the unit-cost real-RAM model (no machine fixed) → one program of the published MatMulTimeLP.RealRAM, Admissible (rational literals; +, −, ×, ÷, comparisons; no square root, no random draw), chosen before the instance and correct on every tape; reason: these are exactly the operations of Proposition 2.3; without draws the run does not depend on the tape
--   - reading: "Algorithm 2.2 can be implemented" (step 1 names its procedure only through Lemma 2.1) → the program's output is the output of some complete run whose directions meet Lemma 2.1's conclusion; reason: the printed algorithm determines a run only up to the choice of directions with those guarantees
--   - reading: no hypothesis on m, n, A printed in this statement → m, n ≥ 1 and columns of Euclidean norm at most 1; reason: the standing hypotheses of Theorem 1.1, under which Algorithm 2.2 is defined to run
--   - encoding: O((mn⁹ + n¹⁰) log(2 + m + n)) additions, subtractions, multiplications, divisions, and comparisons → one constant C (with the program, before the instance) bounding realOps, the number of executed radd, rsub, rmul, rdiv and rblt instructions, and the run halts; reason: O(·) uniform over instances; the paper counts real arithmetic operations and comparisons only
--   - encoding: input A; output ε → input (m, n, A row by row); ε in the first n output cells; reason: the paper fixes no layout
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Proposition 2.3, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_VecBalPoly_layout
import Definitions.Def_VecBalPoly_Alg22Output

namespace VecBalPoly

/-- **Proposition 2.3 (arithmetic cost of Algorithm 2.2).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Proposition 2.3, p.6 (PDF p.7): "Algorithm 2.2 can be implemented deterministically using
O((mn⁹ + n¹⁰) log(2 + m + n)) additions, subtractions, multiplications, divisions, and
comparisons on real numbers."

**Formalization Note** One admissible program `P` and one constant `C`, chosen before the
instance. On input `m, n, A` and every tape it halts, it executes at most
`C(mn⁹ + n¹⁰) log(2 + m + n)` real additions, subtractions, multiplications, divisions and
comparisons (`realOps`), and its first `n` output cells are an output of Algorithm 2.2
(`Alg22Output`: the output of a complete run for some choice of directions meeting Lemma 2.1's
conclusion). The instances are those of Theorem 1.1: `m, n ≥ 1`, column norms at most `1`. -/
theorem proposition_2_3 :
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, (∀ j, ∑ i, A i j ^ 2 ≤ 1) →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout m n A) ω t ∧
        (realOps P (layout m n A) ω t : ℝ) ≤
          C * ((m : ℝ) * (n : ℝ) ^ 9 + (n : ℝ) ^ 10) * Real.log (2 + m + n) ∧
        Alg22Output A (MatMulTimeLP.outputAt P (layout m n A) ω t n) := by sorry

end VecBalPoly
