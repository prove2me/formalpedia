-- Prove2me | Theorems.Thm_RatFunc_trdeg_eq_one
-- name    : RatFunc.trdeg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/f1770f3b-fa3c-536d-994d-408605beaeed
-- title:
--   The rational function field has transcendence degree one
-- statement:
--   For any field $K$ (in an arbitrary universe), the transcendence degree over $K$ of the field $\mathrm{RatFunc}\ K$ of rational functions in one variable — that is, the cardinal $\mathrm{Algebra.trdeg}\ K\ (\mathrm{RatFunc}\ K)$, the common cardinality of a transcendence basis of $\mathrm{RatFunc}\ K$ over $K$ — equals the cardinal $1$. There are no further hypotheses beyond $K$ being a field: the statement is an equality of cardinal numbers, asserting both that $\mathrm{RatFunc}\ K$ is not algebraic over $K$ and that a single element, namely the indeterminate, already generates it up to algebraic dependence.
--
--   This is the standard fact that $K(X)$ is a field of transcendence degree one over $K$. It is used, transported along a $K$-algebra isomorphism, to identify the transcendence degree of function fields arising in the modular-curve models, and is cited in the construction of domains mapping to such function fields in the Deligne–Rapoport model package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RatFunc_trdeg_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem RatFunc.trdeg_eq_one (K : Type u) [Field K] : Algebra.trdeg K (RatFunc K) = 1 := by sorry
