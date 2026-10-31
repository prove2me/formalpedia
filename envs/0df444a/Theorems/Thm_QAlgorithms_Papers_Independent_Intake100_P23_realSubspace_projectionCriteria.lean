-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_realSubspace_projectionCriteria
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.realSubspace_projectionCriteria
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T17:16:27.016679+00:00
-- url     : https://prove2.me/theorems/03795c88-787c-49a9-ab34-a43f6596bb62
-- title:
--   Projection criteria for the position of a real subspace
-- statement:
--   Let $F$ be a complex Hilbert space, regarded as real with inner product $\operatorname{Re}\langle\cdot,\cdot\rangle$. For a closed real subspace $V$, let $P,Q$ be the real orthogonal projections onto $V,iV$, respectively. Write $\perp_{\mathbb R}$ for real orthogonal complement. Then
--   $$\big(V\cap iV=\{0\}\text{ and }V^{\perp_{\mathbb R}}\cap(iV)^{\perp_{\mathbb R}}=\{0\}\big)\iff\ker(P-Q)=\{0\},$$
--   $$V^{\perp_{\mathbb R}}\cap iV=\{0\}\iff\ker(P+Q-1)=\{0\}.$$
--   These are both of the source's general-position criteria. Projection onto $iV$ is distinct from projection onto the symplectic complement.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 61, Theorem 51

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section Projections

open scoped ClosedSubmodule

/-- PDF p.61, Theorem 51: both equivalences, projecting onto V and iV in the
underlying real Hilbert space, not onto a complex span or symplectic complement. -/
theorem realSubspace_projectionCriteria
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : ClosedSubmodule ℝ F) :
    (((V ⊓ V.mulI = ⊥) ∧ (Vᗮ ⊓ V.mulIᗮ = ⊥)) ↔
      LinearMap.ker ((V.toSubmodule.starProjection - V.mulI.toSubmodule.starProjection).toLinearMap) = ⊥) ∧
    ((Vᗮ ⊓ V.mulI = ⊥) ↔
      LinearMap.ker ((V.toSubmodule.starProjection + V.mulI.toSubmodule.starProjection - 1).toLinearMap) = ⊥) := by sorry

end Projections

end QAlgorithms.Papers.Independent.Intake100.P23

end
