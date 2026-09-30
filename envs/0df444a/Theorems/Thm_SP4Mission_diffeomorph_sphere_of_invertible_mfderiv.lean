-- Prove2me | Theorems.Thm_SP4Mission_diffeomorph_sphere_of_invertible_mfderiv
-- name    : SP4Mission.diffeomorph_sphere_of_invertible_mfderiv
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-06T10:42:11.514795+00:00
-- url     : https://prove2.me/theorems/0e9d5372-8cc2-47fa-aa49-b7ef995c7ae2
-- title:
--   Nonsingular smooth homotopy equivalence to the four-sphere is a diffeomorphism
-- statement:
--   Let $S^4$ denote the standard unit sphere in Euclidean five-space. Let $M$ be a compact Hausdorff smooth real four-manifold, with its given smooth atlas, and assume there is a homeomorphism $M\cong S^4$. Let $f:M\to S^4$ be the forward map of a homotopy equivalence. If $f$ is smooth and its differential is invertible at every point, then
--
--   $$\exists d:M\overset{\mathrm{diff}}{\longrightarrow}S^4,\qquad d(x)=f(x)\quad\text{for every }x\in M.$$
--
--   Thus the original map $f$ is a global diffeomorphism. This gives a sufficient condition usable for each manifold in the smooth four-dimensional Poincare conjecture. It does not assert that a nonsingular smooth homotopy equivalence exists for every smooth structure on a topological four-sphere.
-- source:
--   Derived supporting result for SP4Mission.smooth_poincare_4, https://prove2.me/theorems/acb88840-8df8-4040-89df-f387272d80a9. Brian Conrad, Math 396: Bijectivity vs. isomorphism, https://math.stanford.edu/~conrad/diffgeomPage/handouts/cpimmisom.pdf, Theorem 2.1, pp. 1-2; Allen Hatcher, Algebraic Topology, https://pi.math.cornell.edu/~hatcher/AT/AT.pdf, Propositions 1.30 and 1.34, printed pp. 60 and 62; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Topology/Covering/Basic.lean, isLocalHomeomorph_iff_isCoveringMap. This statement is a corollary derived from these results, not a quotation.

import Definitions.Def_SP4Sphere
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Manifold Filter

open ContinuousMap


open SP4Mission

theorem SP4Mission.diffeomorph_sphere_of_invertible_mfderiv
    (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) ∞ M]
    (e : M ≃ₜ S4) (f : M ≃ₕ S4)
    (hf : ContMDiff (𝓡 4) (𝓡 4) ∞ f)
    (hD : ∀ x, (mfderiv (𝓡 4) (𝓡 4) f x).IsInvertible) :
    ∃ d : M ≃ₘ⟮𝓡 4, 𝓡 4⟯ S4, (d : M → S4) = f := by sorry
