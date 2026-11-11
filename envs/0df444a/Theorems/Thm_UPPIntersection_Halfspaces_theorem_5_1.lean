-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_5_1
-- name    : UPPIntersection.Halfspaces.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:55.857942+00:00
-- url     : https://prove2.me/theorems/bd89c59a-a70a-4578-a37a-096e3700bc6f
-- title:
--   Theorem 5.1 — exponentially small average margin for the continuous problem $\mathrm{CHS}_d^{\wedge k}$
-- statement:
--   Let $k\ge2$ be an integer. There are constants $c,C>0$ and $d_0$, depending only on $k$, such that for every $d\ge d_0$, every $r$, and all measurable $f,g:(S^{d-1})^k\to\mathbb R^r$ with $\|f(x)\|_2,\|g(y)\|_2\le1$ everywhere, the following holds. Suppose that for all $x,y\in(S^{d-1})^k$ with $\min_i|\langle x_i,y_i\rangle|>e^{-Cd}$,
--   $$Q_k\bigl(\langle x_1,y_1\rangle,\dots,\langle x_k,y_k\rangle\bigr)\cdot\langle f(x),g(y)\rangle\ge0 .$$
--   Then for independent uniform $X,Y\in(S^{d-1})^k$,
--   $$\mathbb E\bigl[|\langle f(X),g(Y)\rangle|\bigr]\le e^{-cd}.$$
--
--   Every embedding that weakly agrees in sign with the $k$-fold conjunction of continuous halfspaces, away from an exponentially thin band, has exponentially small average margin. This is the continuous core of the sign-rank lower bound.
--
--   Differences from the source:
--   - encoding: independent uniform points of S^{d−1} → the normalized surface measure volume.toSphere / (its total mass) on the unit sphere of EuclideanSpace ℝ (Fin d), and its finite and binary products; reason: this is the rotation-invariant probability measure on the sphere (Solutions/verification proves it has mass one for d ≥ 1)
--   - encoding: min_i |⟨x_i, y_i⟩| > e^{−Cd}; "for all sufficiently large d" → ∀ i, e^{−Cd} < |⟨x_i, y_i⟩|; ∃ d₀ ∀ d ≥ d₀; reason: same conditions; c, C, d₀ are quantified after k and before d, r, f, g
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 25, Theorem 5.1 (eq. (6)); proof pp. 25–27; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Sphere
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

open MeasureTheory

namespace UPPIntersection.Halfspaces

theorem theorem_5_1 (k : ℕ) (hk : 2 ≤ k) : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ d ≥ d₀,
    ∀ (r : ℕ) (f g : (Fin k → Sph d) → EuclideanSpace ℝ (Fin r)),
      Measurable f → Measurable g → (∀ x, ‖f x‖ ≤ 1) → (∀ y, ‖g y‖ ≤ 1) →
      (∀ x y : Fin k → Sph d,
        (∀ i, Real.exp (-C * d) < |inner ℝ (x i : EuclideanSpace ℝ (Fin d)) (y i)|) →
        0 ≤ orthantQ (fun i => inner ℝ (x i : EuclideanSpace ℝ (Fin d)) (y i)) *
          inner ℝ (f x) (g y)) →
      ∫ p : (Fin k → Sph d) × (Fin k → Sph d), |inner ℝ (f p.1) (g p.2)|
        ∂((sphereLawPow d k).prod (sphereLawPow d k)) ≤ Real.exp (-c * d) := by sorry

end UPPIntersection.Halfspaces
