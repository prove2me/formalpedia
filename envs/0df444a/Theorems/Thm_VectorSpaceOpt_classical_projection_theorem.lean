-- Prove2me | Theorems.Thm_VectorSpaceOpt_classical_projection_theorem
-- name    : VectorSpaceOpt.classical_projection_theorem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:23:02.557254+00:00
-- url     : https://prove2.me/theorems/19413330-65ad-41da-a99c-1b65074e7df3
-- title:
--   The classical projection theorem
-- statement:
--   Let $H$ be a real **Hilbert space** and let $M$ be a **closed** subspace of $H$. Then for any vector $x \in H$ there is a **unique** vector $m_0 \in M$ that is closest to $x$:
--
--   $$\exists!\, m_0 \in M \ \text{ such that } \ \|x - m_0\| \le \|x - m\| \quad \text{for all } m \in M.$$
--
--   This is the existence-and-uniqueness half of the projection theorem. Existence is what completeness buys: the proof produces a minimizing sequence, shows it is Cauchy via the parallelogram law, and uses closedness of $M$ to place its limit back in $M$.
--
--   The orthogonality characterization of $m_0$ — that $x - m_0$ is orthogonal to $M$ — is a separate statement, valid already in a pre-Hilbert space and stated there.
--
--   **Formalization Note.** Completeness is assumed of the ambient space and closedness of the subspace separately, matching the source's hypotheses. Uniqueness is part of the assertion, not a corollary left to the reader.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.3, Theorem 2, p. 51

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem classical_projection_theorem {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (x : H) :
    ∃! m₀ : H, m₀ ∈ M ∧ ∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖ := by sorry

end VectorSpaceOpt
