-- Prove2me | Theorems.Thm_VectorSpaceOpt_min_norm_linear_variety
-- name    : VectorSpaceOpt.min_norm_linear_variety
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:24:39.179929+00:00
-- url     : https://prove2.me/theorems/c5f421a6-fd6a-4be0-ac29-63132762037d
-- title:
--   Minimum norm over a linear variety
-- statement:
--   Let $M$ be a **closed** subspace of a real Hilbert space $H$, let $x \in H$ be fixed, and let
--
--   $$V = x + M$$
--
--   be the **linear variety** obtained by translating $M$ by $x$. Then there is a **unique** vector $x_0 \in V$ of minimum norm, and it is orthogonal to $M$:
--
--   $$\|x_0\| \le \|v\| \ \text{ for all } v \in V, \qquad \langle x_0,\, m\rangle = 0 \ \text{ for all } m \in M.$$
--
--   The result is the projection theorem restated: translating $V$ by $-x$ turns it into the closed subspace $M$, and the minimum-norm point of $V$ corresponds to the projection of $-x$ onto $M$.
--
--   One point deserves care. The minimum-norm solution $x_0$ is orthogonal to the **subspace $M$** from which the variety is built — *not* to the variety $V$ itself. Confusing the two is the standard error here, and the source flags it explicitly.
--
--   **Formalization Note.** Membership in $V$ is written as the existence of an $m \in M$ with $x_0 = x + m$; existence, minimality, and orthogonality are asserted jointly as a single unique-existence claim.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.10, Theorem 1, p. 64

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem min_norm_linear_variety {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) (x : H) :
    ∃! x₀ : H, (∃ m ∈ M, x₀ = x + m) ∧
      (∀ v : H, (∃ m ∈ M, v = x + m) → ‖x₀‖ ≤ ‖v‖) ∧
      (∀ m ∈ M, ⟪x₀, m⟫ = 0) := by sorry

end VectorSpaceOpt
