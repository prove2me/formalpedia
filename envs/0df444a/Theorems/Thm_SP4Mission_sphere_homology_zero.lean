-- Prove2me | Theorems.Thm_SP4Mission_sphere_homology_zero
-- name    : SP4Mission.sphere_homology_zero
-- status  : Open
-- author  : @ryanshin
-- created : 2026-09-09T02:57:46.076232+00:00
-- url     : https://prove2.me/theorems/5ca8aaac-bcfd-4af3-8972-2878093d3778
-- title:
--   Homology of spheres: $H_k(S^n;\mathbb Z)=0$ for $k\ge1$, $k\ne n$
-- statement:
--   Let $S^n\subset\mathbb R^{n+1}$ be the unit sphere, $n\ge0$. Then the integral singular homology of $S^n$ vanishes in every positive degree other than $n$:
--
--   $$
--   H_k(S^n;\mathbb Z)=0\qquad\text{for all } k\ge1,\ k\ne n .
--   $$
--
--   Together with $H_0(S^n)\cong\mathbb Z$ ($n\ge1$) and $H_n(S^n)\cong\mathbb Z$ this is the complete computation of the homology of spheres (Hatcher, Corollary 2.14: $\tilde H_n(S^n)\cong\mathbb Z$ and $\tilde H_i(S^n)=0$ for $i\ne n$). The standard proof uses the long exact sequence of the pair $(D^{n+1},S^n)$ or the Mayer–Vietoris sequence for the cover of $S^n$ by two open hemispheres, and induction on $n$. In the mission the case $n=4$ is used: $H_k(S^4;\mathbb Z)=0$ for $k\in\{1,2,3\}$ and $k\ge5$.
--
--   **Formalization Note** The sphere is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1`, so that `S4` of the mission is literally the case `n = 4`; homology is `SP4Homology.H k`, and vanishing is `IsZero` in `ModuleCat ℤ`. Only the vanishing clauses of Corollary 2.14 are stated; the case $k=0$ is excluded since $H_0(S^n)\cong\mathbb Z$ for $n\ge1$.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Corollary 2.14, p. 114: "H̃ₙ(Sⁿ) ≈ Z and H̃ᵢ(Sⁿ) = 0 for i ≠ n" (vanishing clause, in positive degrees, so that reduced and unreduced homology agree).

import Definitions.Def_SP4Sphere
import Definitions.Def_SP4WeakHomotopy
import Definitions.Def_SP4Homology
import Definitions.Def_SP4HomologyMap

set_option autoImplicit false

open scoped Manifold ContDiff
open SP4Mission CategoryTheory Limits

theorem SP4Mission.sphere_homology_zero (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≠ n) :
    IsZero (SP4Homology.H k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) := by sorry
