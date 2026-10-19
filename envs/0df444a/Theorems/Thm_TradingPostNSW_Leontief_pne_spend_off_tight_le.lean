-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_pne_spend_off_tight_le
-- name    : TradingPostNSW.Leontief.pne_spend_off_tight_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:12.620071+00:00
-- url     : https://prove2.me/theorems/7fde02ca-2a20-4d6c-afd3-ad24d36b0e6d
-- title:
--   Proof of Theorem 4.7, pp. 15–16 — at a PNE of TP(∆) an agent spends at most (m − 1)∆ outside its tight set S_i
-- statement:
--   Consider an instance satisfying the standing assumptions and perfect competition, an entrance fee $0 < \Delta < 1/m$, and a pure Nash equilibrium $b$ of $\mathcal{TP}(\Delta)$ with tight sets $S_i$ as above. Then for every agent $i$
--   $$\sum_{j \in M \setminus S_i} b_{i,j} \;\le\; (m-1)\,\Delta .$$
--
--   Since agent $i$ bids $B_i$ in total, at least $B_i - (m-1)\Delta$ is spent on its tight goods; this is what bounds the gain of any deviation by a factor $1+\epsilon$ in Theorem 4.7.
--
--   **Formalization Note** The sum runs over all goods outside $S_i$, including undemanded ones. The page's sentence continues "thus $i$ spends at most $B_i - (m-1)\Delta$ on the remaining items in $S_i$"; by the budget identity that amount is a lower bound, and only the first half of the sentence is stated. $m$ is cast to $\mathbb{R}$, so $m - 1$ is real subtraction.
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, pp. 15–16, proof of Theorem 4.7

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting

namespace TradingPostNSW.Leontief

/-- Proof of Theorem 4.7, pp. 15–16: at a pure Nash equilibrium of `TP(Δ)`, agent `i` spends
at most `(m − 1)Δ` on the goods outside its tight set `S_i`. -/
theorem pne_spend_off_tight_le {n m : ℕ} (I : Instance n m) (Δ : ℝ) (b : Fin n → Fin m → ℝ)
    (hI : Standing I) (hPC : PerfectCompetition I) (hΔ : 0 < Δ) (hΔm : Δ < 1 / (m : ℝ))
    (hb : IsPNE I Δ b) :
    ∀ i, ∑ j ∈ Finset.univ \ tight I Δ b i, b i j ≤ ((m : ℝ) - 1) * Δ := by sorry

end TradingPostNSW.Leontief
