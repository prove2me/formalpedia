-- Prove2me | Theorems.Thm_UPPIntersection_Halfspaces_Supplement_theorem_8_5
-- name    : UPPIntersection.Halfspaces.Supplement.theorem_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:05:31.531991+00:00
-- url     : https://prove2.me/theorems/aaaa357c-e6b4-4bef-84e1-fc6e4716dd71
-- title:
--   Theorem 8.5 — tightness of Theorem 7.1: $\mathrm{rank}_\pm(HS_{M,d})\ge d$ and $\mathrm{rank}_\pm(HS_{M,d}\wedge HS_{M,d})\le2^{O(d+\log M)}$
-- statement:
--   For all positive integers $d$ and $M$,
--   $$\operatorname{rank}_\pm(HS_{M,d})\ge d,\qquad\operatorname{rank}_\pm(HS_{M,d}\wedge HS_{M,d})\le2^{O(d+\log M)}.$$
--   In particular, the lower bound of Theorem 7.1 is tight when $M=2^{\Theta(d)}$.
--
--   Here $HS_{M,d}(a,b)=\operatorname{sgn}(\langle a,b\rangle-1/2)$ on $a,b\in\{-M,\dots,M\}^d$ (Definition 1.1), and $\log$ is base 2.
--
--   **Formalization Note** The $O$-term is a universal constant $K>0$, chosen before $d$ and $M$, with $\operatorname{rank}_\pm(HS_{M,d}\wedge HS_{M,d})\le2^{K(d+\log_2M)}$. The "in particular" clause is stated as: there are $c,C>0$ and $d_0$ such that for every $A>0$ there is $K'>0$ with $e^{cd}\le\operatorname{rank}_\pm(HS_{M,d}\wedge HS_{M,d})\le2^{K'd}$ for all $d\ge d_0$ and $\lceil e^{Cd}\rceil\le M\le2^{Ad}$; the lower half is the content of Theorem 7.1 for the same range.
--
--   Differences from the source:
--   - encoding: 2^{O(d + log M)} → 2^{K(d + log₂ M)} for one universal K > 0 chosen before d and M; reason: the O-constant is universal in the source; d + log₂ M ≥ 1 for positive d, M
--   - encoding: the lower bound of Theorem 7.1 is tight when M = 2^{Θ(d)} → ∃ c, C > 0, d₀ ∀ A > 0 ∃ K' > 0: e^{cd} ≤ rank_±(HS∧HS) ≤ 2^{K'd} for d ≥ d₀ and ⌈e^{Cd}⌉ ≤ M ≤ 2^{Ad}; reason: this is the meaning of tightness: Theorem 7.1's lower bound e^{cd} holds from M ≥ ⌈e^{Cd}⌉ on, and for M ≤ 2^{Ad} the upper bound is 2^{O(d)}
-- source:
--   Mark Bun, Mandar Juvekar, STOC 2027 submission #478 (October 2026), p. 32, Theorem 8.5 (proof on pp. 32–33); PDF page = printed page; source.pdf SHA-256 1d258c38a48636b0aa03fa9dfce0ba5e367df8b9c55ee6e67f9f3b6f76e0d388

import Mathlib
import Definitions.Def_SignRankMargin_OREquality_SignRank
import Definitions.Def_UPPIntersection_Halfspaces_SignMatrices

open SignRankMargin.OREquality

namespace UPPIntersection.Halfspaces.Supplement

/-- Bun–Juvekar, Theorem 8.5 (p. 32). For all positive integers `d` and `M`,
`rank_±(HS_{M,d}) ≥ d` and `rank_±(HS_{M,d} ∧ HS_{M,d}) ≤ 2^{K(d + log₂ M)}` for a universal `K > 0`
(i.e. `2^{O(d + log M)}`). In particular the lower bound of Theorem 7.1 is tight when `M = 2^{Θ(d)}`:
there are `c, C > 0` and `d₀` such that for every `A > 0` there is `K' > 0` with
`e^{c d} ≤ rank_±(HS_{M,d} ∧ HS_{M,d}) ≤ 2^{K' d}` whenever `d ≥ d₀` and `⌈e^{C d}⌉ ≤ M ≤ 2^{A d}`. -/
theorem theorem_8_5 :
    (∀ M d : ℕ, 0 < M → 0 < d → d ≤ signRank (HS M d)) ∧
    (∃ K : ℝ, 0 < K ∧ ∀ M d : ℕ, 0 < M → 0 < d →
      (signRank (andSquare (HS M d)) : ℝ) ≤ (2 : ℝ) ^ (K * ((d : ℝ) + Real.logb 2 M))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ d₀ : ℕ, ∀ A : ℝ, 0 < A → ∃ K' : ℝ, 0 < K' ∧
      ∀ d ≥ d₀, ∀ M : ℕ, ⌈Real.exp (C * d)⌉₊ ≤ M → (M : ℝ) ≤ (2 : ℝ) ^ (A * d) →
        Real.exp (c * d) ≤ (signRank (andSquare (HS M d)) : ℝ) ∧
        (signRank (andSquare (HS M d)) : ℝ) ≤ (2 : ℝ) ^ (K' * d)) := by sorry

end UPPIntersection.Halfspaces.Supplement
