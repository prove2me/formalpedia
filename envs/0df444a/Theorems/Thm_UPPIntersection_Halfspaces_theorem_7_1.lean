-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_theorem_7_1
-- name    : UPPIntersection.Halfspaces.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:58.622712+00:00
-- url     : https://prove2.me/theorems/98f3ae91-a302-4521-a6b0-17c3ee2d8593
-- title:
--   Theorem 7.1 — sign rank of $HS_{M,d}$ and $HS_{M,d}\wedge HS_{M,d}$, and the communication consequence
-- statement:
--   There are universal constants $c,C>0$ such that:
--
--   1. for all natural $M,d\ge1$ with $M\ge\lceil e^{Cd}\rceil$, $\operatorname{rank}_\pm(HS_{M,d})\le d+1$;
--   2. there is $d_0$ such that for all $d\ge d_0$ and all $M\ge\lceil e^{Cd}\rceil$, $\operatorname{rank}_\pm(HS_{M,d}\wedge HS_{M,d})\ge e^{cd}$;
--   3. consequently, with $M=\lceil e^{Cd}\rceil$ and $n=d\,\lceil\log_2(2M+1)\rceil$ the number of bits encoding one row (or column) of $HS_{M,d}$,
--   $$U(HS_{M,d})=O(\log n)\qquad\text{and}\qquad U(HS_{M,d}\wedge HS_{M,d})=\Omega(\sqrt n),$$
--   that is, there are $A,B$ with $U(HS_{M,d})\le A\log_2n+B$ for all $d\ge1$, and $c'>0$, $d_1$ with $U(HS_{M,d}\wedge HS_{M,d})\ge c'\sqrt n$ for all $d\ge d_1$.
--
--   Here $HS_{M,d}(a,b)=\operatorname{sgn}(\langle a,b\rangle-1/2)$ on the full grid $\{-M,\dots,M\}^d$. This is the main theorem in sign-rank form, from which Theorem 1.2 is restated.
--
--   Differences from the source:
--   - encoding: sign values in {−1, 1}, with −1 meaning logical true → Bool entries with true standing for +1 (as in the published SignRankMargin sign-rank definition); reason: a relabelling of the two values; the signed AND (−1 iff both are −1) becomes Boolean OR of the stored bits, and sign representation becomes A·R > 0 entrywise
--   - encoding: two-party protocols in which both players have an unlimited sequence of private random bits → deterministic protocol trees (published DetCCHard.Protocol) over (input, private tape) pairs, tape = an infinite sequence of independent fair bits (product measure), every bit function measurable in the speaker's tape; cost = tree depth; U = least cost of a protocol that is correct on each input with probability > 1/2; reason: this is the operational model of the source; measurability is what makes the success probability of a protocol defined at all
--   - reading: the protocol's output (the source does not say which party announces it) → the output is the label of the leaf reached, i.e. it is determined by the transcript; reason: the standard convention; any other convention changes U by at most one bit, which every statement here absorbs in its additive constant
--   - reading: U = O(log n) and U = Ω(√n) for the family M = ⌈e^{Cd}⌉ → ∃ A B ∀ d ≥ 1, U ≤ A log₂ n + B; ∃ c' > 0 ∃ d₁ ∀ d ≥ d₁, U ≥ c'√n; reason: the asymptotic notation over d → ∞; finitely many small d are absorbed by the additive constant B
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 29, Theorem 7.1 (proof §7.1, pp. 29–30); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_Communication
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices

open SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces

theorem theorem_7_1 : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    (∀ M d : ℕ, 0 < d → ⌈Real.exp (C * d)⌉₊ ≤ M → signRank (HS M d) ≤ d + 1) ∧
    (∃ d₀ : ℕ, ∀ d ≥ d₀, ∀ M : ℕ, ⌈Real.exp (C * d)⌉₊ ≤ M →
      Real.exp (c * d) ≤ (signRank (andSquare (HS M d)) : ℝ)) ∧
    (∃ A B : ℝ, ∀ d : ℕ, 0 < d →
      (U (HS ⌈Real.exp (C * d)⌉₊ d) : ℝ) ≤
        A * Real.logb 2 (encodingLength ⌈Real.exp (C * d)⌉₊ d) + B) ∧
    (∃ c' : ℝ, 0 < c' ∧ ∃ d₁ : ℕ, ∀ d ≥ d₁,
      c' * Real.sqrt (encodingLength ⌈Real.exp (C * d)⌉₊ d) ≤
        (U (andSquare (HS ⌈Real.exp (C * d)⌉₊ d)) : ℝ)) := by sorry

end UPPIntersection.Halfspaces
