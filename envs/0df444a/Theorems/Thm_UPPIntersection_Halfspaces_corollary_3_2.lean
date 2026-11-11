-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_corollary_3_2
-- name    : UPPIntersection.Halfspaces.corollary_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:40.511196+00:00
-- url     : https://prove2.me/theorems/137830cc-99d0-4b82-a334-d9ab0f612556
-- title:
--   Corollary 3.2 — Taylor remainder bound for $H_{f,g}$ at the origin
-- statement:
--   Let $f,g:(S^{d-1})^k\to\mathbb R^r$ be measurable with $\|f(x)\|_2,\|g(y)\|_2\le1$ everywhere, and $H=H_{f,g}$. Let $D$ be an integer with $0<D\le\lfloor(d-2)/2\rfloor-1$, and let $T_D$ be the Taylor polynomial of $H$ at the origin consisting of the terms of total degree at most $D$. Then for every $s\in[-1/4,1/4]^k$,
--   $$|H(s)-T_D(s)|\le(4\|s\|_1)^{D+1}.$$
--
--   This is the only result of Section 3 used later: near the origin, $H$ is uniformly close to a low-degree polynomial whatever $f$ and $g$ are.
--
--   Differences from the source:
--   - encoding: experiment D_s: V_i uniform on the unit sphere of X_i^⊥, independently, and Y_i = s_i X_i + √(1 − s_i²) V_i → V_i = w_i/‖w_i‖ with w_i = U_i − ⟨U_i, X_i⟩X_i for an independent uniform U_i ∈ S^{d−1}; on the null event where the resulting Y_i is not a unit vector (U_i = ±X_i) Y_i := X_i; reason: for d ≥ 2, conditional on X_i the normalized projection of a uniform point is uniform on the great subsphere orthogonal to X_i (invariance under rotations fixing X_i), and the fallback event has probability zero, so H_{f,g} is the same function on all of [−1,1]^k; the integrand is measurable (proved in Solutions/verification)
--   - encoding: independent uniform points of S^{d−1} → the normalized surface measure volume.toSphere / (its total mass) on the unit sphere of EuclideanSpace ℝ (Fin d), and its finite and binary products; reason: this is the rotation-invariant probability measure on the sphere (Solutions/verification proves it has mass one for d ≥ 1)
--   - encoding: partial derivatives ∂^α H = ∂_1^{α_1} ⋯ ∂_k^{α_k} H → multiPartial α H: iterated one-variable derivatives along the coordinate lines, ∂_k applied first; reason: on the open box where H is C^m these are the classical mixed partials, and the order is the source's
--   - encoding: 0 < D ≤ ⌊(d − 2)/2⌋ − 1 → 0 < D and D + 1 ≤ (d − 2)/2 in natural-number arithmetic; reason: the two are equivalent for natural D > 0, and this form avoids truncated subtraction; it forces d ≥ 6, so d ≥ 2 needs no separate hypothesis
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 15, Corollary 3.2; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere

open MeasureTheory

namespace UPPIntersection.Halfspaces

theorem corollary_3_2 (d k r : ℕ)
    (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r))
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : ∀ x, ‖f x‖ ≤ 1) (hg1 : ∀ y, ‖g y‖ ≤ 1)
    (D : ℕ) (hD : 0 < D) (hDd : D + 1 ≤ (d - 2) / 2) :
    ∀ s ∈ Set.Icc (fun _ : Fin k => -(1 / 4 : ℝ)) (fun _ => 1 / 4),
      |symH f g s - taylorPoly (symH f g) D s| ≤ (4 * ∑ i, |s i|) ^ (D + 1) := by sorry

end UPPIntersection.Halfspaces
