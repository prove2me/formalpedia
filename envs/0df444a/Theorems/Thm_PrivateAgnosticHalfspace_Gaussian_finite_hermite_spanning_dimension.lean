-- Prove2me | Theorems.Thm_PrivateAgnosticHalfspace_Gaussian_finite_hermite_spanning_dimension
-- name    : PrivateAgnosticHalfspace.Gaussian.finite_hermite_spanning_dimension
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T21:20:39.149211+00:00
-- url     : https://prove2.me/theorems/be06efa5-cc11-41ef-a4ee-b9a13d25f44b
-- title:
--   Finite tensor Hermite spanning and dimension
-- statement:
--   Let $d,p\in\mathbb N_0$. For each multi-index $\kappa\in\mathbb N_0^d$ with $|\kappa|\le p$, let $h_\kappa$ be the normalized tensor probabilists' Hermite polynomial. Then every real polynomial function on $\mathbb R^d$ of total degree at most $p$ is a linear combination of these functions, and conversely every such linear combination has total degree at most $p$. The number of these multi-indices is
--   $$
--   \#\{\kappa\in\mathbb N_0^d:|\kappa|\le p\}=\binom{d+p}{p}.
--   $$
--   This is the finite algebraic part of the Gaussian Hermite basis lemma. It identifies the coefficient-vector representation and its exact feature dimension independently of the analytic completeness statement.
-- source:
--   Giorgio Racca, Amartya Sanyal, Vikrant Singhal, Privacy for Free in Efficient Agnostic Halfspace Learning, STOC 2027 submission #1006, p.22, Lemma B.8, final sentence; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1006.pdf, SHA-256 f0122a33e29daa624b530bdd0b071998d8e44197b30449b0cb3213289645cec7

import Definitions.Def_PrivateAgnosticHalfspace_Gaussian_Regression
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
set_option autoImplicit false
open PrivateAgnosticHalfspace.Gaussian

theorem PrivateAgnosticHalfspace.Gaussian.finite_hermite_spanning_dimension (d p : ℕ) :
    polynomialFunctions d p = Set.range (polynomialPredictor d p) ∧
    Fintype.card (Index d p) = featureDimension d p := by sorry
