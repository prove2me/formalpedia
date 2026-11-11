-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_corollary_6_4
-- name    : UPPIntersection.Halfspaces.corollary_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:57.954078+00:00
-- url     : https://prove2.me/theorems/7b4c6f0e-e551-4886-889e-0efe5c20e3d5
-- title:
--   Corollary 6.4 — transfer from the sphere to the discrete conjunction $B\wedge B$
-- statement:
--   There are constants $c,C>0$ and $d_0$ such that for every $d\ge d_0$ the following holds. Let $B$ be a sign matrix with finite row set $\mathcal A$ and column set $\mathcal B$, and suppose there are measurable maps $\pi_1:S^{d-1}\to\mathcal A$ and $\pi_2:S^{d-1}\to\mathcal B$ such that
--   $$B_{\pi_1(x),\pi_2(y)}=\operatorname{sgn}\langle x,y\rangle\qquad\text{for all }x,y\in S^{d-1}\text{ with }|\langle x,y\rangle|>e^{-Cd}.$$
--   Then
--   $$\operatorname{rank}_\pm(B\wedge B)\ge e^{cd}.$$
--
--   Any finite matrix that discretizes the continuous halfspace problem, up to an exponentially thin band, has exponentially large sign rank after a disjoint conjunction. Theorem 7.1 applies it to $HS_{M,d}$ with $\pi(x)=\mathrm{round}(Mx)$.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: measurable maps π₁, π₂ into finite sets; "sufficiently large d" → measurable fibers; ∃ d₀ ∀ d ≥ d₀; reason: same notions; c, C, d₀ precede d, the matrix and the maps
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 28, Corollary 6.4 (proof pp. 28–29); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices
import Definitions.Def_UPPIntersection_Halfspaces_Sphere

open MeasureTheory SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces

theorem corollary_6_4 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ {X Y : Type} [Fintype X] [Fintype Y] (B : Matrix X Y Bool)
      (π₁ : Sph d → X) (π₂ : Sph d → Y),
      (∀ a, MeasurableSet (π₁ ⁻¹' {a})) → (∀ b, MeasurableSet (π₂ ⁻¹' {b})) →
      (∀ x y : Sph d, Real.exp (-C * d) < |inner ℝ (x : EuclideanSpace ℝ (Fin d)) y| →
        B (π₁ x) (π₂ y) = decide (0 < inner ℝ (x : EuclideanSpace ℝ (Fin d)) y)) →
      Real.exp (c * d) ≤ (signRank (andSquare B) : ℝ) := by sorry

end UPPIntersection.Halfspaces
