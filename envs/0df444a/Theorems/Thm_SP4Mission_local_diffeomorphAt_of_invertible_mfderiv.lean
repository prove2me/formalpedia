-- Prove2me | Theorems.Thm_SP4Mission_local_diffeomorphAt_of_invertible_mfderiv
-- name    : SP4Mission.local_diffeomorphAt_of_invertible_mfderiv
-- status  : Proved
-- author  : @evgeth
-- created : 2026-09-06T10:41:45.533582+00:00
-- url     : https://prove2.me/theorems/21dc5957-1dc6-404d-9a29-d620f45c957e
-- title:
--   Smooth manifold inverse function theorem at a nonsingular point
-- statement:
--   Let $M$ and $N$ be smooth real manifolds without boundary, modeled on real normed spaces $E$ and $F$, respectively, with $E$ complete. Let $f:M\to N$ be smooth and let $x\in M$. Suppose its differential is a continuous linear isomorphism:
--
--   $$D f_x:T_xM\overset{\sim}{\longrightarrow}T_{f(x)}N.$$
--
--   Then there are open neighborhoods $U$ of $x$ and $V$ of $f(x)$ such that
--
--   $$f|_U:U\overset{\sim}{\longrightarrow}V$$
--
--   is a smooth diffeomorphism. The given smooth atlases are retained.
--
--   This is the smooth inverse function theorem for boundaryless manifolds, including all finite-dimensional real manifolds. The differential assumption itself implies that $F$ is complete.
--
--   **Formalization Note** Smoothness is assumed for the map on its whole domain; invertibility is required only at the selected point. The conclusion includes smoothness of the inverse on a single open neighborhood.
-- source:
--   Manifold inverse function theorem, smooth boundaryless version. Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474, Geometry/Manifold/LocalDiffeomorph.lean, TODO at lines 43-46, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Geometry/Manifold/LocalDiffeomorph.lean#L43; Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean, ContDiffAt.toOpenPartialHomeomorph (lines 33-35), and Analysis/Calculus/ContDiff/Operations.lean, OpenPartialHomeomorph.contDiffAt_symm (lines 887-891). This is the real Banach-model manifold consequence of the cited inverse function theorem, with global smoothness to ensure a smooth inverse on one neighborhood. For the finite-dimensional local-to-global setting, see Brian Conrad, Math 396: Bijectivity vs. isomorphism, https://math.stanford.edu/~conrad/diffgeomPage/handouts/cpimmisom.pdf, Theorem 2.1, pp. 1-2.

import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

set_option autoImplicit false

open scoped Manifold ContDiff Topology
open Set Manifold Filter

set_option backward.isDefEq.respectTransparency false

theorem SP4Mission.local_diffeomorphAt_of_invertible_mfderiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [ChartedSpace E M] [ChartedSpace F N]
    [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N]
    {f : M → N} {x : M}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (hD : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x).IsInvertible) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by sorry
