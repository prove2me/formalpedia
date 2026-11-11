-- Prove2me | Theorems.Thm_PostedPriceLimits_FullRevelation_no_constant_approximation
-- name    : PostedPriceLimits.FullRevelation.no_constant_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:39:51.174632+00:00
-- url     : https://prove2.me/theorems/fa397b7e-146a-4e2a-be74-5aa89339a22d
-- title:
--   Theorem 1.1 — posted prices cannot guarantee an $O(1)$-approximation for XOS bidders
-- statement:
--   Posted price mechanisms cannot guarantee an $O(1)$-approximation of the welfare in combinatorial auctions with XOS valuations.
--
--   Precisely: let $M_{n,m}$ be any family of randomized online full-revelation mechanisms, one for each number $n$ of bidders and $m$ of items. Each visits the bidders one at a time in an adaptively chosen (possibly random) order, posts to the visited bidder a price vector $p\in[0,\infty]^m$ with previously allocated items priced $+\infty$, allocates the bidder's lexicographically smallest utility-maximizing bundle, and then learns that bidder's full valuation; it may use unbounded computation and arbitrary randomness. Then for every constant $C$ there are $n$, $m$ and an XOS profile $v_1,\dots,v_n$ (fixed before the mechanism's randomness) with
--   $$C\cdot\mathbb E\Big[\sum_{i\in[n]}v_i(S_i)\Big]<\max_{(T_1,\dots,T_n)}\sum_{i\in[n]}v_i(T_i),$$
--   where $(S_1,\dots,S_n)$ is the mechanism's allocation and the maximum ranges over all allocations. Hence no family of posted price mechanisms attains a $C$-approximation over all dimensions, for any constant $C$.
--
--   This answers negatively whether the $O(\log\log m)$ guarantee of the best known posted price mechanisms can be improved to a constant, even for sellers with full view of previous valuations.
--
--   Differences from the source:
--   - reading: cannot guarantee an O(1)-approximation → for every mechanism family M and every constant C there are n, m and an XOS profile with C·E[welfare] < OPT; reason: the negation of a dimension-independent constant guarantee in the sense of Definition 3.6; the profile is fixed before the mechanism's randomness
--   - encoding: posted price (OFR) mechanisms with adaptive order, randomization, unbounded computation → RandOFR: a probability space of seeds and a deterministic history-based mechanism per seed, with welfare measurable in the seed; an optional next-bidder proposal has fallback to the smallest unvisited bidder and stops when no bidder remains; reason: every source mechanism is represented, including the empty auction at n = 0; measurability only makes the expectation defined
--   - generalization: approximation constants C ≥ 1 → every real constant C; reason: the witness for C = 1 also works for every C ≤ 1 because expected welfare is nonnegative; all source approximation constants remain included
-- source:
--   Frederick Qiu, Aviad Rubinstein, STOC 2027 submission #1596 (October 2026), Theorem 1.1, p.1 (PDF 2); model Definitions 3.1–3.6, p.5 (PDF 6); PDF SHA-256 5be77a250fd554b42d30cff15c46dafe3e43c75a2d90968fae98c61ff1113bb3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1596.pdf

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_PostedPriceLimits_FullRevelation_Model
open ComplementFreeCA.XOSGreedy

namespace PostedPriceLimits.FullRevelation

/-- Theorem 1.1. Posted price mechanisms cannot guarantee an `O(1)`-approximation of the
welfare in combinatorial auctions with XOS valuations: for every family of randomized online
full-revelation mechanisms (one for each number of bidders `n` and items `m`) and every
constant `C`, some XOS profile has `C · E[welfare] < OPT`. -/
theorem no_constant_approximation (M : (n m : ℕ) → RandOFR n m) (C : ℝ) :
    ∃ (n m : ℕ) (E : Fin n → XOSExpr m), C * expectedWelfare (M n m) E < optWelfare E := by sorry

end PostedPriceLimits.FullRevelation
