-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_lemma_4_1
-- name    : UPPIntersection.Halfspaces.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:39.806122+00:00
-- url     : https://prove2.me/theorems/58796af6-b730-4f10-b8de-fa567b200ca8
-- title:
--   Lemma 4.1 — coefficient bound for approximate sign representations of $Q_k$
-- statement:
--   There are universal constants $c,C>0$ (independent of $k$ and $D$) such that the following holds. Let $k\ge2$ and $D\ge1$ be integers and set $\eta=e^{-D/C}$. Let $p(s)=\sum_{|\alpha|\le D}\lambda_\alpha s^\alpha$ be a real polynomial in $k$ variables of total degree at most $D$. If
--   $$Q_k(s)\,p(s)\ge-1\qquad\text{for all }s\in I_\eta^k,$$
--   then for every multi-index $\alpha$,
--   $$|\lambda_\alpha|\le e^{cD^2+D\ln(40k)} .$$
--
--   A polynomial that nearly sign-represents the orthant function outside thin bands around the coordinate hyperplanes must have small coefficients; combined with Corollary 3.2 this bounds the continuous average margin in Theorem 5.1.
--
--   Differences from the source: none.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 21, Lemma 4.1 (proof pp. 24–25); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces

theorem lemma_4_1 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ k D : ℕ, 2 ≤ k → 1 ≤ D → ∀ p : MvPolynomial (Fin k) ℝ, p.totalDegree ≤ D →
      (∀ s : Fin k → ℝ, (∀ i, s i ∈ bandI (Real.exp (-(D : ℝ) / C))) →
        -1 ≤ orthantQ s * MvPolynomial.eval s p) →
      ∀ α : Fin k →₀ ℕ, |p.coeff α| ≤ Real.exp (c * (D : ℝ) ^ 2 + D * Real.log (40 * k)) := by sorry

end UPPIntersection.Halfspaces
