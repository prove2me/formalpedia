-- Prove2me | Theorems.Thm_VecBalPoly_theorem_1_1
-- name    : VecBalPoly.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:11:01.101159+00:00
-- url     : https://prove2.me/theorems/38b99af2-9bc2-4756-9ba3-5bec0fd0f985
-- title:
--   Theorem 1.1 — a deterministic polynomial-time real-RAM algorithm for Komlós discrepancy at most 8272
-- statement:
--   There is a deterministic algorithm in the unit-cost real-RAM model that, given any $m,n\ge1$ and $A=[a_1\cdots a_n]\in\mathbb R^{m\times n}$ with $\|a_j\|_2\le1$ for every column, returns signs $\varepsilon\in\{-1,1\}^n$ with
--   $$\|A\varepsilon\|_\infty\le 8272,$$
--   and its running time is polynomial in $m$ and $n$.
--
--   The Komlós conjecture asserts that the discrepancy of such matrices is bounded by an absolute constant; this theorem finds such a signing efficiently.
--
--   **Formalization Note** One admissible program and constants $C,k$ are fixed before the instance. On the input $(m,n,A)$ and every tape the program halts at a step $t$ with $t+1\le C(m+n+2)^k$, every executed instruction counted, and its first $n$ output cells hold $\varepsilon$.
--
--   Differences from the source:
--   - reading: "a deterministic algorithm" in "the unit-cost real-RAM model" (no machine fixed) → one program of the published MatMulTimeLP.RealRAM, Admissible (rational literals; +, −, ×, ÷, comparisons; no square root, no random draw), chosen before m, n, A and correct on every tape; reason: the operations the paper lists (Proposition 2.3); without draws the run does not depend on the tape
--   - encoding: "polynomial running time" → total steps t + 1 ≤ C(m + n + 2)^k, every executed instruction counted, C and k fixed with the program; reason: the input has mn + 2 reals, and a polynomial in m + n is a polynomial in the input size
--   - encoding: input A; output ε → input (m, n, A row by row); ε in the first n output cells; reason: the paper fixes no layout
--   - encoding: ‖a_j‖₂ ≤ 1, ε ∈ {−1, 1}ⁿ, ‖Aε‖∞ ≤ 8272 → Σ_i A i j² ≤ 1; each output cell is 1 or −1; |Σ_j A i j ε_j| ≤ 8272 for every row i; reason: the same conditions written coordinatewise
--   - encoding: indices i ∈ [m], j ∈ [n] → Fin m, Fin n (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Theorem 1.1, p.1 (PDF p.2)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_layout

namespace VecBalPoly

/-- **Theorem 1.1 (deterministic constant-discrepancy Komlós signing in polynomial time).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Theorem 1.1, p.1 (PDF p.2): "There is a deterministic algorithm that, given any
m, n ≥ 1 and A ∈ ℝ^{m×n} with ∥aj∥2 ≤ 1 for every column aj, returns ε ∈ {−1, 1}^n satisfying
∥Aε∥∞ ≤ 8272. The algorithm has polynomial running time in the unit-cost real-RAM model."

**Formalization Note** One admissible program `P` of the published unit-cost real RAM (rational
literals; addition, subtraction, multiplication, division, comparison; no square root, no random
draw) and constants `C, k`, all chosen before the instance. On input `m, n, A` (row by row) and
every tape `ω`, it halts at a step `t` with total running time `t + 1 ≤ C(m + n + 2)^k`
(every instruction counted), and its first `n` output cells hold signs `ε` with
`|(Aε)ᵢ| ≤ 8272` for every row. Column norms are written `∑ᵢ A i j ² ≤ 1`. -/
theorem theorem_1_1 :
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C k : ℕ,
      ∀ (m n : ℕ), 1 ≤ m → 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℝ, (∀ j, ∑ i, A i j ^ 2 ≤ 1) →
      ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout m n A) ω t ∧
        t + 1 ≤ C * (m + n + 2) ^ k ∧
        (∀ j, MatMulTimeLP.outputAt P (layout m n A) ω t n j = 1 ∨
              MatMulTimeLP.outputAt P (layout m n A) ω t n j = -1) ∧
        ∀ i, |∑ j, A i j * MatMulTimeLP.outputAt P (layout m n A) ω t n j| ≤ 8272 := by sorry

end VecBalPoly
