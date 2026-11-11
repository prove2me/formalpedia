-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_lemma_4_2
-- name    : UPPIntersection.Halfspaces.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:47.526711+00:00
-- url     : https://prove2.me/theorems/ea0313a9-5b63-44df-b049-fcfb21218ff2
-- title:
--   Lemma 4.2 — degree lower bound for rational approximation of sgn on $I_\eta$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Let $\eta\in(0,1)$ and let $k\ge2$ be an integer. If $p,q$ are real univariate polynomials of degree at most $D$ such that for every $x\in I_\eta=[-1,-\eta]\cup[\eta,1]$ we have $q(x)\ne0$ and
--   $$\Bigl|\frac{p(x)}{q(x)}-\operatorname{sgn}x\Bigr|\le\frac1k,$$
--   then
--   $$D\ge2C\ln(2k-1)\ln(1/\eta).$$
--
--   This is a lower bound, implicit in Newman's work on rational approximation of $|x|$; it feeds the degree lower bound for sign representations of $Q_k$ in Lemma 4.4.
--
--   Differences from the source:
--   - encoding: degree bound D (a number) → D a natural number with natDegree p, natDegree q ≤ D; reason: degrees are natural numbers, so for a real bound D the statement for ⌊D⌋ (or for max(deg p, deg q)) gives it and conversely
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 21, Lemma 4.2; proof in Appendix A.3, pp. 40–41; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces

theorem lemma_4_2 : ∃ C : ℝ, 0 < C ∧
    ∀ η : ℝ, 0 < η → η < 1 → ∀ k : ℕ, 2 ≤ k →
      ∀ (D : ℕ) (p q : Polynomial ℝ), p.natDegree ≤ D → q.natDegree ≤ D →
        (∀ x ∈ bandI η, q.eval x ≠ 0 ∧ |p.eval x / q.eval x - Real.sign x| ≤ 1 / (k : ℝ)) →
        2 * C * Real.log (2 * (k : ℝ) - 1) * Real.log (1 / η) ≤ D := by sorry

end UPPIntersection.Halfspaces
