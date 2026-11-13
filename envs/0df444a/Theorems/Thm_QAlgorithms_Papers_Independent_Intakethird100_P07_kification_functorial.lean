-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P07_kification_functorial
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P07.kification_functorial
-- status  : Proved
-- author  : @Gohan
-- created : 2026-11-01T04:30:54.426113+00:00
-- url     : https://prove2.me/theorems/101db8c1-ea3a-46e2-809c-9736156885a0
-- title:
--   B.k-functor
-- statement:
--   For continuous maps $f:X\to Y$ and $g:Y\to Z$ of arbitrary topological spaces, the same underlying function $k(f):kX\to kY$ is continuous. Moreover
--
--   $$k(f)(x)=f(x),\qquad k(\operatorname{id}_X)=\operatorname{id}_{kX},\qquad k(g\circ f)=k(g)\circ k(f).$$
--
--   Together with the final compact-Hausdorff-probe topology on objects, these maps define the specified functor $k:\mathrm{Top}\to\mathrm{kTop}$. No separation condition is imposed.
-- source:
--   Cohomology of Local Cochains, arXiv:1110.2661v2, PDF p. 36, B.k-functor

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P07

noncomputable section

universe u v

namespace QAlgorithms.Papers.Independent.Intakethird100.P07

open CategoryTheory Topology TopologicalSpace

/-- The unnumbered k-functor assertion after B.4, PDF p. 36: continuity,
identity-on-points, and the identity and composition laws for the concrete lift. -/
theorem kification_functorial
    (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) :
    Continuous (kMap f) ∧
    (∀ x : KSpace X, kMap f x = f x) ∧
    kMap (ContinuousMap.id X) = ContinuousMap.id (KSpace X) ∧
    kMap (g.comp f) = (kMap g).comp (kMap f) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P07

end
