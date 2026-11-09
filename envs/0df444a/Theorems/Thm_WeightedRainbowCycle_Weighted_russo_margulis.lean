-- Prove2me | Theorems.Thm_WeightedRainbowCycle_Weighted_russo_margulis
-- name    : WeightedRainbowCycle.Weighted.russo_margulis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:05:37.125805+00:00
-- url     : https://prove2.me/theorems/4de21af9-1f99-40f0-8c10-8b3d0924def6
-- title:
--   Fact 3.8 — Russo–Margulis for every real-valued set function
-- statement:
--   Let $S$ be any finite set, including the empty set, and let $f:2^S\to\mathbb R$ be arbitrary. Identify subsets with Boolean membership vectors. For any real $q$, let $F(q)=\mathbb E_q f(A)$ denote the Bernoulli polynomial; for $0\le q\le1$, this is expectation under independent inclusion of each element with probability $q$. Then
--
--   $$F'(q)=\mathbb E_q\left[\sum_{c\in S}\bigl(f(A\cup\{c\})-f(A\setminus\{c\})\bigr)\right].$$
--
--   The statement includes differentiability of $F$ at $q$. No monotonicity, sign, indicator-value, or bounded-by-one restriction is placed on $f$. This is the full summed identity needed for the boundary derivative estimate; the published first-partial formula is an auxiliary reference, not a replacement for it.
--
--   Differences from the source:
--   - reading: probability p in the preamble but q in the formula, with index s and summand c → one parameter q and the same bound coordinate c in insertion and deletion; reason: resolves inconsistent dummy variables; c denotes a singleton when inserted or removed
--   - generalization: Bernoulli expectation on the probability interval → the same finite polynomial and its derivative for all real q; reason: specializes to the entire probabilistic interval, including polynomial derivatives at both endpoints
--   - encoding: f on subsets and a displayed derivative equality → f on Boolean membership vectors and HasDerivAt of the published bernExp polynomial; reason: the finite sum is exactly the independent Bernoulli expectation and HasDerivAt also records its automatic differentiability
-- source:
--   Andrew D. Lin, STOC 2027 submission #545 (October 2026), Fact 3.8 (Russo-Margulis Formula, citing Theorem 2.32 of [Gri99]), p. 7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/545.pdf

import Definitions.Def_DiffNeighbors_Bias_Model
import Theorems.Thm_DiffNeighbors_Bias_first_partial

set_option autoImplicit false

namespace WeightedRainbowCycle.Weighted

/-- Fact 3.8, p. 7, for the finite Bernoulli polynomial on every real q. -/
theorem russo_margulis {S : Type*} [Fintype S] [DecidableEq S]
    (f : (S → Bool) → ℝ) (q : ℝ) :
    HasDerivAt (fun p => DiffNeighbors.Bias.bernExp p f)
      (DiffNeighbors.Bias.bernExp q (fun z => ∑ c : S,
        (f (Function.update z c true) - f (Function.update z c false)))) q := by sorry

end WeightedRainbowCycle.Weighted
