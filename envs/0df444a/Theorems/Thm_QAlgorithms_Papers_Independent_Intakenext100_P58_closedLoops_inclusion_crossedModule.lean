-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P58_closedLoops_inclusion_crossedModule
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P58.closedLoops_inclusion_crossedModule
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T06:47:28.279077+00:00
-- url     : https://prove2.me/theorems/116150b4-39a0-4fcb-8a45-22001a74e2f5
-- title:
--   Closed-loop inclusion is a right crossed module of underlying groupoids
-- statement:
--   Let $\Gamma_1\rightrightarrows\Gamma_0$ be a Lie groupoid with source $s$ and target $t$. Write
--   $$
--   S\Gamma=\{x\in\Gamma_1:s(x)=t(x)\},\qquad p(x)=s(x)=t(x).
--   $$
--   The fibre of $p$ over an object $m$ is its isotropy group, with the multiplication, identity and inverse inherited from $\Gamma$. Let $i:S\Gamma\hookrightarrow\Gamma_1$ be the inclusion. For $p(x)=t(\gamma)$ define the right conjugation action
--   $$
--   x^\gamma=\gamma^{-1}x\gamma.
--   $$
--   Then $p:S\Gamma\to\Gamma_0$, $i$ and this action form a crossed module of underlying groupoids. In particular the action is by group isomorphisms between the appropriate fibres, and
--   $$
--   i(x^\gamma)=\gamma^{-1}i(x)\gamma,\qquad x^{i(y)}=y^{-1}xy\quad\text{when }p(x)=p(y).
--   $$
--   This identifies the canonical isotropy-family crossed module of a Lie groupoid. It asserts no manifold structure on $S\Gamma$.
--
--   **Formalization Note** The Lie groupoid carries boundaryless finite-dimensional real manifold structures and smooth groupoid operations, with surjective-submersion source and target. Fibre operations and the action are constrained only on their composable domains.
-- source:
--   G-gerbes, principal 2-group bundles and characteristic classes, arXiv:0801.1238v3, PDF p. 6, Example 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P58

namespace QAlgorithms.Papers.Independent.Intakenext100.P58

open scoped Manifold ContDiff

universe u v w

/-- Example 2.5, arXiv:0801.1238v3, PDF p. 6 (Definition 2.3 on p. 5).
For a Lie groupoid, its actual closed arrows form a family of groups; the
inclusion into the underlying groupoid, with right conjugation, is a crossed
module. No manifold structure on the closed-loop set is concluded. -/
theorem closedLoops_inclusion_crossedModule
    {n0 n1 : ℕ} {M : Type u} {A : Type v}
    [TopologicalSpace M] [TopologicalSpace A]
    [ChartedSpace (EuclideanSpace ℝ (Fin n0)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n1)) A]
    (D : GroupoidData M A) (hLie : IsLieGroupoid (n0 := n0) (n1 := n1) D) :
    IsRightCrossedModule D (loopBase D) (loopUnit D) (loopInverse D)
      (loopMultiply D) (loopInclusion D) (loopConjugate D) := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P58
