-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_lemma_2_3
-- name    : UPPIntersection.Halfspaces.Supplement.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:02:17.10481+00:00
-- url     : https://prove2.me/theorems/ce6135d3-36b9-4ce2-861c-8412306adba4
-- title:
--   Lemma 2.3 — $N\ge e^{bd^2}$ random points form an $e^{-ad}$-net of $S^{d-1}$ except with probability $1/N$
-- statement:
--   For every constant $a>0$ there is a constant $b>0$ such that the following holds for all sufficiently large $d$ and every integer $N\ge e^{bd^2}$: if $X_1,\dots,X_N$ are independent uniformly random points of $S^{d-1}$, then
--   $$\Pr\Big[\exists\,y\in S^{d-1}\ \forall i\in[N]:\ \|y-X_i\|_2>e^{-ad}\Big]\le\frac1N.$$
--
--   Thus exponentially-in-$d^2$ many random points cover the sphere at exponentially small scale with high probability; this is how the random matrices of Theorem 7.2 inherit the conjunction lower bound of Corollary 6.4.
--
--   **Formalization Note** The probability is the (outer) measure of the bad event under the $N$-fold product of the uniform law, as an extended nonnegative real.
--
--   Differences from the source: none.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 14, Lemma 2.3 (stated on pp. 13–14 with a reference to the proof of [Kob23, Lemma 3.2]); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere

open MeasureTheory

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Lemma 2.3 (p. 14). For every `a > 0` there is `b > 0` such that for all sufficiently
large `d` and every `N ≥ e^{b d²}`, the probability over independent uniform `X₁, …, X_N ∈ S^{d-1}`
that some `y ∈ S^{d-1}` has `‖y - X_i‖₂ > e^{-a d}` for every `i` is at most `1/N`. -/
theorem lemma_2_3 (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ N : ℕ, Real.exp (b * (d : ℝ) ^ 2) ≤ N →
      sphereLawPow d N {X : Fin N → Sph d | ∃ y : Sph d, ∀ i,
          Real.exp (-a * d) < ‖(y : EuclideanSpace ℝ (Fin d)) - (X i : EuclideanSpace ℝ (Fin d))‖}
        ≤ (N : ENNReal)⁻¹ := by sorry

end UPPIntersection.Halfspaces.Supplement
