-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_3_1
-- name    : UPPIntersection.Halfspaces.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:44.471387+00:00
-- url     : https://prove2.me/theorems/cbcb85f4-d9b2-415d-8d75-1396ba6ac5e6
-- title:
--   Theorem 3.1 — smoothness and derivative bounds for the spherical symmetrization $H_{f,g}$
-- statement:
--   Let $d\ge2$, $k,r\ge0$, and let $f,g:(S^{d-1})^k\to\mathbb R^r$ be measurable with $\|f(x)\|_2\le1$ and $\|g(y)\|_2\le1$ for all $x,y$. Let $H=H_{f,g}$ be the spherical symmetrization and $m=\lfloor(d-2)/2\rfloor$. Then
--
--   1. $H$ is continuous on $[-1,1]^k$;
--   2. $H$ is $m$ times continuously differentiable on $(-1,1)^k$;
--   3. for every multi-index $\alpha$ with $|\alpha|\le m$ and every $s\in[-1/4,1/4]^k$,
--   $$\frac{|\partial^\alpha H(s)|}{\alpha!}\le4^{|\alpha|}.$$
--
--   No continuity of $f,g$ is assumed: the averaging over $D_s$ alone produces the smoothness. This is the quantitative input for the Taylor estimate of Corollary 3.2.
--
--   Differences from the source:
--   - encoding: experiment D_s: V_i uniform on the unit sphere of X_i^⊥, independently, and Y_i = s_i X_i + √(1 − s_i²) V_i → V_i = w_i/‖w_i‖ with w_i = U_i − ⟨U_i, X_i⟩X_i for an independent uniform U_i ∈ S^{d−1}; on the null event where the resulting Y_i is not a unit vector (U_i = ±X_i) Y_i := X_i; reason: for d ≥ 2, conditional on X_i the normalized projection of a uniform point is uniform on the great subsphere orthogonal to X_i (invariance under rotations fixing X_i), and the fallback event has probability zero, so H_{f,g} is the same function on all of [−1,1]^k; the integrand is measurable (proved in Solutions/verification)
--   - encoding: independent uniform points of S^{d−1} → the normalized surface measure volume.toSphere / (its total mass) on the unit sphere of EuclideanSpace ℝ (Fin d), and its finite and binary products; reason: this is the rotation-invariant probability measure on the sphere (Solutions/verification proves it has mass one for d ≥ 1)
--   - encoding: partial derivatives ∂^α H = ∂_1^{α_1} ⋯ ∂_k^{α_k} H → multiPartial α H: iterated one-variable derivatives along the coordinate lines, ∂_k applied first; reason: on the open box where H is C^m these are the classical mixed partials, and the order is the source's
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 14, Theorem 3.1; proof §3.3, p. 20, using Proposition 3.4 (p. 16), Theorem 3.5 (p. 17), Lemma 3.6 (p. 18), Theorem 3.7 (pp. 18–19); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere

open MeasureTheory

namespace UPPIntersection.Halfspaces

theorem theorem_3_1 (d k r : ℕ) (hd : 2 ≤ d)
    (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r))
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ‖f x‖ ≤ 1) (hg1 : ∀ y, ‖g y‖ ≤ 1) :
    ContinuousOn (symH f g) (Set.Icc (fun _ => -1) (fun _ => 1)) ∧
      ContDiffOn ℝ ((d - 2) / 2 : ℕ) (symH f g) (Set.pi Set.univ fun _ => Set.Ioo (-1) 1) ∧
      ∀ α : Fin k → ℕ, ∑ i, α i ≤ (d - 2) / 2 →
        ∀ s ∈ Set.Icc (fun _ : Fin k => -(1 / 4 : ℝ)) (fun _ => 1 / 4),
          |multiPartial α (symH f g) s| / (multiFact α : ℝ) ≤ 4 ^ (∑ i, α i) := by sorry

end UPPIntersection.Halfspaces
