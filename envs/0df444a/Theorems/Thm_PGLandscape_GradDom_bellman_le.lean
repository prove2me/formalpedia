-- Prove2me | Theorems.Thm_PGLandscape_GradDom_bellman_le
-- name    : PGLandscape.GradDom.bellman_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:09.632064+00:00
-- url     : https://prove2.me/theorems/a95fefec-c437-470f-a745-aedce56ef89d
-- title:
--   (5), p. 7 — TJ ⪯ T_πJ and TJ_π ⪯ J_π
-- statement:
--   Let $\pi\in\Pi$ be a feasible policy and $J$ a bounded measurable function on $\mathcal S$. Then, element-wise,
--   $$TJ\preceq T_\pi J\qquad\text{and}\qquad TJ_\pi\preceq J_\pi. \tag{5}$$
--   Here $T_\pi$ and $T$ are the Bellman operator and the Bellman optimality operator, and $J_\pi$ is the cost-to-go of $\pi$.
--
--   The first inequality says that the minimum over feasible actions is at most the value of the action chosen by $\pi$; the second combines it with the fixed-point equation $T_\pi J_\pi=J_\pi$. Both are used repeatedly, for example to identify $\|J_\pi-TJ_\pi\|_{1,\nu}$ with $\int (J_\pi-TJ_\pi)\,d\nu$.
--
--   **Formalization Note** "$J\in\mathcal J$" is encoded as $J$ measurable and bounded. The page prints (3) and (4) without the factor $\gamma$; the factor is restored, as in (6), (7), Assumption 2 and every proof (without it $T$ has no fixed point $J^*$).
-- source:
--   arXiv:1906.01786v3, (5), p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.GradDom

open MeasureTheory ProbabilityTheory

/-- (5), p. 7: for `π ∈ Π` and every bounded measurable `J`, `TJ ⪯ T_π J`; and `TJ_π ⪯ J_π`. -/
theorem bellman_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) (J : S → ℝ) (hJm : Measurable J)
    (hJb : ∃ C : ℝ, ∀ s, |J s| ≤ C) :
    (∀ s, PGLandscape.Closure.bellmanOpt M J s ≤ PGLandscape.Closure.bellmanPi M π.1 J s) ∧
      (∀ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s ≤ PGLandscape.Closure.costToGo M π s) := by sorry

end PGLandscape.GradDom
