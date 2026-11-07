-- Prove2me | Theorems.Thm_VecBalPoly_lemma_D_2
-- name    : VecBalPoly.lemma_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T23:10:50.558922+00:00
-- url     : https://prove2.me/theorems/22729b24-53b7-471a-af82-b98b9411cd82
-- title:
--   Lemma D.2 — a negative quadratic direction in $O(s^3)$ operations
-- statement:
--   There is a deterministic real-RAM procedure that, given a symmetric matrix $Q\in\mathbb R^{s\times s}$ with a negative eigenvalue, finds a vector $z$ with
--   $$z^{\mathsf T}Qz<0$$
--   using $O(s^3)$ real arithmetic operations and comparisons.
--
--   The procedure avoids computing eigenvalues; Lemma 2.1 applies it to the approximate Hessian restricted to the constraint space.
--
--   Differences from the source:
--   - reading: "a deterministic procedure" / "can be implemented" in the unit-cost real-RAM model (no machine fixed) → one program of the published MatMulTimeLP.RealRAM, Admissible (rational literals; +, −, ×, ÷, comparisons; no square root, no random draw), chosen before the instance and correct on every tape; reason: these are exactly the operations of Proposition 2.3; without draws the run does not depend on the tape
--   - encoding: O(s³) arithmetic operations and comparisons → one constant C (with the program, before the instance) bounding realOps, the number of executed radd, rsub, rmul, rdiv and rblt instructions, and the run halts; reason: O(·) uniform over instances; the paper counts real arithmetic operations and comparisons only
--   - encoding: the input Q and the output z → input (s, Q row by row); z in the first s output cells; reason: the paper fixes no layout
--   - encoding: indices j ∈ [s] → Fin s (0-based); reason: Lean convention; same instances
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), Lemma D.2, p.17 (PDF p.18)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps

namespace VecBalPoly

open Matrix

/-- **Lemma D.2 (a negative quadratic direction without eigenvalues).**
Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), Lemma D.2, p.17 (PDF p.18): "Given a symmetric matrix Q ∈ ℝ^{s×s} with a negative
eigenvalue, a vector z with zᵀQz < 0 can be found in O(s³) arithmetic operations and
comparisons."

**Formalization Note** One admissible program `P` and one constant `C`, chosen before the
instance. The input is the real `s` followed by `Q` row by row; the output is the first `s`
cells after the input. The count is of real arithmetic operations and comparisons
(`realOps`). -/
theorem lemma_D_2 :
    ∃ P : MatMulTimeLP.Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (s : ℕ) (Q : Matrix (Fin s) (Fin s) ℝ), Q.IsSymm →
        (∃ μ : ℝ, μ < 0 ∧ Module.End.HasEigenvalue (Matrix.toLin' Q) μ) →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ,
          MatMulTimeLP.HaltsAt P ([(s : ℝ)] ++ MatMulTimeLP.matToList Q) ω t ∧
          (realOps P ([(s : ℝ)] ++ MatMulTimeLP.matToList Q) ω t : ℝ) ≤ C * (s : ℝ) ^ 3 ∧
          MatMulTimeLP.outputAt P ([(s : ℝ)] ++ MatMulTimeLP.matToList Q) ω t s ⬝ᵥ
            (Q *ᵥ MatMulTimeLP.outputAt P ([(s : ℝ)] ++ MatMulTimeLP.matToList Q) ω t s) < 0 := by sorry

end VecBalPoly
