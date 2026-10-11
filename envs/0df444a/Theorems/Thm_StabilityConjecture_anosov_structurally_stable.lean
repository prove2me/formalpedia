-- Prove2me | Theorems.Thm_StabilityConjecture_anosov_structurally_stable
-- name    : StabilityConjecture.anosov_structurally_stable
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T09:00:56.403613+00:00
-- url     : https://prove2.me/theorems/2661a238-7950-465b-ab1a-5a5c1db3d208
-- title:
--   Anosov diffeomorphisms are $C^r$ structurally stable
-- statement:
--   Let $M$ be a closed manifold: a compact Hausdorff smooth manifold without boundary, modelled on $\mathbb R^n$. Let $r\ge 1$ and let $f\in\mathrm{Diff}^r(M)$ be an Anosov diffeomorphism: $M$ itself is a hyperbolic set of $f$. Then $f$ is $C^r$ structurally stable: there is a neighbourhood $\mathcal U$ of $f$ in $\mathrm{Diff}^r(M)$ such that every $g\in\mathcal U$ is topologically conjugate to $f$,
--
--   $$\exists\, h\colon M\to M \text{ homeomorphism with } h\circ f=g\circ h .$$
--
--   This is the first and simplest case of the converse direction of the Palis–Smale conjecture: hyperbolicity implies structural stability.
-- source:
--   D. V. Anosov, Geodesic flows on closed Riemannian manifolds with negative curvature, Proc. Steklov Inst. Math. 90 (1967). Context: Open Problem Garden, "C^r Stability Conjecture" (Conjecture, author(s) J. Palis and S. Smale; posted by m n, December 20th, 2007), https://www.openproblemgarden.org/op/c_r_stability_conjecture

import Mathlib
import Definitions.Def_ClosingLemma_DiffeoCrTopology
import Definitions.Def_PughClosingLemma_nonwandering
import Definitions.Def_StabilityConjecture_Basic

open scoped Manifold ContDiff Topology

namespace StabilityConjecture

open ClosingLemma

theorem anosov_structurally_stable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (r : ℕ) (hr : 1 ≤ r) (f : Diff n M r) (hf : IsAnosov f) :
    IsStructurallyStable r f := by sorry

end StabilityConjecture
