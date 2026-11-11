-- Prove2me | Theorems.Thm_OrderedSearchExact_Exact_lemma_4_2
-- name    : OrderedSearchExact.Exact.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:03.223174+00:00
-- url     : https://prove2.me/theorems/fab6cb0c-c7a5-4c74-857b-31d10d898cbf
-- title:
--   Lemma 4.2 — exact positivity
-- statement:
--   For every integer $n\ge2$ and every rate $\lambda\in[0,\infty]$, the normalized hyperbolic solution polynomial obeys
--
--   $$G_{\lambda,n}(e^{i\theta})\ge0\qquad(\theta\in\mathbb R).$$
--
--   Both limiting rates are included. This is the positivity foundation for the continuous packet family.
--
--   Differences from the source:
--   - encoding: normalized real symmetric Laurent polynomials of degree less than n → real coefficient vectors indexed by Fin (n-1), with frequency i+1 and evaluation on every real angle; reason: this bijects the source coefficients, preserves the constant coefficient 1, and includes all points of the unit circle
--   - encoding: rates in [0,infinity], with limiting endpoints → ENNReal rates with explicit zero and infinity branches; reason: the extended supremum never defaults to a finite real value; the endpoint polynomials are the prescribed limits
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Lemma 4.2, p.13 (PDF p.13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Packets

namespace OrderedSearchExact.Exact

theorem lemma_4_2 (n : ℕ) (hn : 2 ≤ n) (lam : Rate) :
    Nonnegative (g n lam) := by sorry

end OrderedSearchExact.Exact
