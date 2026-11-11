-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_lemma_4_6
-- name    : UPPIntersection.Halfspaces.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:26:55.384075+00:00
-- url     : https://prove2.me/theorems/556366f8-bff0-495f-b9dd-4f9b0f5a338d
-- title:
--   Lemma 4.6 — coefficients of a polynomial are bounded by its $L^1$ norm on $[1,2]^k$
-- statement:
--   Let $k,D\ge1$ and let $p(s)=\sum_{|\alpha|\le D}\lambda_\alpha s^\alpha$ be a real polynomial in $k$ variables of total degree at most $D$. Then for every multi-index $\alpha$,
--   $$|\lambda_\alpha|\le(40k)^D\int_{[1,2]^k}|p(s)|\,ds ,$$
--   the integral being with respect to Lebesgue measure on $\mathbb R^k$.
--
--   This converts an integral lower bound into a coefficient bound and is the bridge from the degree lower bound of Lemma 4.4 to the coefficient bound of Lemma 4.1.
--
--   Differences from the source: none.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 23, Lemma 4.6 (proof pp. 23–24); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib

open MeasureTheory

namespace UPPIntersection.Halfspaces

theorem lemma_4_6 (k D : ℕ) (hk : 1 ≤ k) (hD : 1 ≤ D) (p : MvPolynomial (Fin k) ℝ)
    (hp : p.totalDegree ≤ D) (α : Fin k →₀ ℕ) :
    |p.coeff α| ≤ (40 * (k : ℝ)) ^ D *
      ∫ s in Set.Icc (fun _ : Fin k => (1 : ℝ)) (fun _ => 2), |MvPolynomial.eval s p| := by sorry

end UPPIntersection.Halfspaces
