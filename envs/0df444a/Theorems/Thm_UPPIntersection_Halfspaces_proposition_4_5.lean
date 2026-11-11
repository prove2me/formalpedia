-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_proposition_4_5
-- name    : UPPIntersection.Halfspaces.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:46.739357+00:00
-- url     : https://prove2.me/theorems/d3de789a-477f-4630-9aaf-bf82d72a7020
-- title:
--   Proposition 4.5 — orthogonality, boundedness and coefficient size of the shifted Legendre polynomials $L_i$
-- statement:
--   Let $L_i(t)=\sum_{a=0}^{i}\binom ia^2(t-1)^a(t-2)^{i-a}$. Then:
--
--   1. for all $i,j\ge0$,
--   $$\int_1^2L_i(t)L_j(t)\,dt=\begin{cases}\dfrac1{2i+1}&i=j,\\[4pt]0&\text{otherwise;}\end{cases}$$
--   2. for all $i$ and $t\in[1,2]$, $|L_i(t)|\le1$;
--   3. the sum of the absolute values of the monomial coefficients of $L_i$ is at most $12^i$.
--
--   All three clauses are stated. They are the facts behind the coefficient bound of Lemma 4.6.
--
--   Differences from the source: none.
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 22, Proposition 4.5; proof in Appendix A.4, pp. 41–43; PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_UPPIntersection_Halfspaces_Polynomials

namespace UPPIntersection.Halfspaces

theorem proposition_4_5 :
    (∀ i j : ℕ, ∫ t in (1 : ℝ)..2, (shiftedL i).eval t * (shiftedL j).eval t =
      if i = j then 1 / (2 * (i : ℝ) + 1) else 0) ∧
    (∀ i : ℕ, ∀ t ∈ Set.Icc (1 : ℝ) 2, |(shiftedL i).eval t| ≤ 1) ∧
    (∀ i : ℕ, ∑ n ∈ (shiftedL i).support, |(shiftedL i).coeff n| ≤ 12 ^ i) := by sorry

end UPPIntersection.Halfspaces
