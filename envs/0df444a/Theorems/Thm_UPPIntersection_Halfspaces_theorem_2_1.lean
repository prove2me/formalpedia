-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_2_1
-- name    : UPPIntersection.Halfspaces.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:50.050201+00:00
-- url     : https://prove2.me/theorems/b9a58530-b484-4789-a851-7404b7613af0
-- title:
--   Theorem 2.1 — Paturi–Simon: $U(F)=\log\operatorname{rank}_\pm(M_F)\pm O(1)$
-- statement:
--   There is an absolute constant $K$ such that for every $n$ and every function $F:\{-1,1\}^n\times\{-1,1\}^n\to\{-1,1\}$ with communication matrix $M_F(x,y)=F(x,y)$,
--   $$\bigl|U(F)-\log_2\operatorname{rank}_\pm(M_F)\bigr|\le K ,$$
--   where $U(F)$ is the unbounded-error (private-coin, success probability $>1/2$ on each input) communication complexity and $\operatorname{rank}_\pm$ is sign rank.
--
--   This equivalence is what turns the sign-rank bounds of Theorem 7.1 into the communication bounds of the headline theorem.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: two-party protocols in which both players have an unlimited sequence of private random bits → deterministic protocol trees (published DetCCHard.Protocol) over (input, private tape) pairs, tape = an infinite sequence of independent fair bits (product measure), every bit function measurable in the speaker's tape; cost = tree depth; U = least cost of a protocol that is correct on each input with probability > 1/2; reason: this is the operational model of the source; measurability is what makes the success probability of a protocol defined at all
--   - reading: the protocol's output (the source does not say which party announces it) → the output is the label of the leaf reached, i.e. it is determined by the transcript; reason: the standard convention; any other convention changes U by at most one bit, which every statement here absorbs in its additive constant
--   - reading: U(F) = log(rank±(M_F)) ± O(1) → ∃ K, ∀ n, ∀ F, |U(F) − log₂ rank±(M_F)| ≤ K; reason: O(1) is an absolute additive constant, uniform in n and F; log is base 2 by the paper's convention (p. 12)
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 13, Theorem 2.1 ([PS86]); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_Communication

open SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces

theorem theorem_2_1 : ∃ K : ℝ, ∀ (n : ℕ) (F : (Fin n → Bool) → (Fin n → Bool) → Bool),
    |(U F : ℝ) - Real.logb 2 (signRank (F : Matrix (Fin n → Bool) (Fin n → Bool) Bool) : ℝ)| ≤ K := by sorry

end UPPIntersection.Halfspaces
