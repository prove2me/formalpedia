-- Prove2me | Theorems.Thm_Section5SignMoments_covarianceTracePolynomial_degree
-- name    : Section5SignMoments.covarianceTracePolynomial_degree
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:07:56.092048+00:00
-- url     : https://prove2.me/theorems/df7f1548-b5da-4ea1-8c63-9f1c77c0fd6a
-- title:
--   Degree of the covariance trace polynomial
-- statement:
--   Let $I,J$ be finite index sets, let $S$ be a real $I\times I$ matrix, and let $p\in\mathbb N$. The polynomial in variables indexed by $J\times I$ representing the trace of the $2p$th power of the centered empirical covariance has total degree bounded by
--
--   $$\deg P_{S,p}\le4p.$$
--
--   This permits bounded-degree moment transfer for covariance trace moments.
-- source:
--   Original auxiliary result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5 (formalization support, not an assertion that the paper states this auxiliary lemma verbatim). Exact formalization: Solutions/Section5CovarianceTracePolynomial.lean, lines 52–58.

import Definitions.Def_Section5Verified_Section5CovarianceTracePolynomial
import Mathlib
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι J σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

theorem Section5SignMoments.covarianceTracePolynomial_degree (S : Matrix ι ι ℝ) (p : ℕ) :
    (Section5SignMoments.covarianceTracePolynomial (J := J) S p).totalDegree ≤ 4*p := by sorry
