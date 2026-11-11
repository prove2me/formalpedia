-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_proposition_2_2
-- name    : UPPIntersection.Halfspaces.proposition_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:35.418428+00:00
-- url     : https://prove2.me/theorems/27c69b90-939e-4415-bdf3-fe04ddde8d23
-- title:
--   Proposition 2.2 — tail bounds for the inner product of two random unit vectors
-- statement:
--   Let $d\ge2$ and let $X,Y$ be independent uniform points of the unit sphere $S^{d-1}\subseteq\mathbb R^d$, with $S=\langle X,Y\rangle$. Then for every $\delta\in(0,1)$:
--   $$\frac12(1-\delta^2)^{d-1}\le\Pr\bigl[|S|\ge\delta\bigr]\le\frac1\delta(1+\delta^2)^{-(d-1)/2},$$
--   $$\Pr\bigl[|S|\le\delta\bigr]\le2\delta\sqrt d .$$
--
--   All three bounds are stated. The anti-concentration bound $\Pr[|S|\le\delta]\le2\delta\sqrt d$ is what lets the continuous margin argument discard the thin band where $|\langle x_i,y_i\rangle|$ is exponentially small.
--
--   Differences from the source:
--   - encoding: independent uniform points of S^{d−1} → the normalized surface measure volume.toSphere / (its total mass) on the unit sphere of EuclideanSpace ℝ (Fin d), and its finite and binary products; reason: this is the rotation-invariant probability measure on the sphere (Solutions/verification proves it has mass one for d ≥ 1)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 13, Proposition 2.2 (eqs. (2), (3)); proof in Appendix A.1, pp. 36–37; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere

open MeasureTheory

namespace UPPIntersection.Halfspaces

theorem proposition_2_2 (d : ℕ) (hd : 2 ≤ d) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (1 / 2) * (1 - δ ^ 2) ^ (d - 1) ≤
        ((sphereLaw d).prod (sphereLaw d)).real
          {p : Sph d × Sph d | δ ≤ |inner ℝ (p.1 : EuclideanSpace ℝ (Fin d)) p.2|} ∧
      ((sphereLaw d).prod (sphereLaw d)).real
          {p : Sph d × Sph d | δ ≤ |inner ℝ (p.1 : EuclideanSpace ℝ (Fin d)) p.2|} ≤
        δ⁻¹ * (1 + δ ^ 2) ^ (-((d : ℝ) - 1) / 2) ∧
      ((sphereLaw d).prod (sphereLaw d)).real
          {p : Sph d × Sph d | |inner ℝ (p.1 : EuclideanSpace ℝ (Fin d)) p.2| ≤ δ} ≤
        2 * δ * Real.sqrt d := by sorry

end UPPIntersection.Halfspaces
