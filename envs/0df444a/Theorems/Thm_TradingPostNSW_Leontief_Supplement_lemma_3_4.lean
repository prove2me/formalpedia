-- Prove2me | Theorems.Thm_TradingPostNSW_Leontief_Supplement_lemma_3_4
-- name    : TradingPostNSW.Leontief.Supplement.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:30:52.581053+00:00
-- url     : https://prove2.me/theorems/39bfcfd9-97c9-4e0e-9da4-40de30658270
-- title:
--   Lemma 3.4, p. 8 (corrected: other buyers report a positive value) — a unilateral report change raises the prices of the goods that got dearer by at most B_i
-- statement:
--   Consider a Fisher market with linear (additive) reported valuations $r_{k,j}\ge0$ and budgets $B_k\ge1$. Let $(p,x)$ be a market equilibrium of the reported market, and suppose buyer $i$ unilaterally changes its report to $r'_i\ge0$; let $(p',x')$ be any market equilibrium of the new reported market. Assume that every buyer $k\ne i$ reports a positive value for at least one good. Then the goods whose price strictly increased satisfy
--   $$\sum_{j:\ p'_j>p_j} p'_j\ \le\ B_i+\sum_{j:\ p'_j>p_j}p_j .$$
--
--   Both equilibria are arbitrary; uniqueness of equilibrium prices is not assumed. The lemma bounds the effect of a single buyer's misreport on prices and is the step of Theorem 3.3 that converts a deviation into a price comparison.
--
--   Differences from the source:
--   - correction: the bound holds for every report profile → every buyer k ≠ i reports a positive value for some good; reason: false as printed: with two buyers, three goods, B = 1, buyer k reporting 0, r_i = (1,1,0), p = (1,1,0) (k buys good 1, i good 2) and r'_i = (0,0,1), p' = (0,0,2) (both buy good 3) are equilibria, and Σ_{p'_j>p_j} p'_j = 2 > 1 + 0; the proof's Lin1 step needs v_{k,β} > 0, i.e. a buyer that values something (DISPROOF.md)
--   - reading: optimal bundle: ∀ y with y·p ≤ B_i → ∀ y ≥ 0 with p·y ≤ B_i; reason: bundles are quantities of goods; this is the reading of the published base mission
-- source:
--   Brânzei, Gkatzelis, Mehta, Nash Social Welfare Approximation for Strategic Agents, arXiv:1607.01569v3, p. 8, Lemma 3.4; proof p. 8

import Mathlib
import Definitions.Def_TradingPostNSW_Leontief_Setting
import Definitions.Def_TradingPostNSW_Leontief_Supplement_Setting

namespace TradingPostNSW.Leontief.Supplement

theorem lemma_3_4 {n m : ℕ} (I : Instance n m) (hI : GenStanding I)
    (r : Fin n → Fin m → ℝ) (hr : ∀ k j, 0 ≤ r k j) (i : Fin n) (r' : Fin m → ℝ)
    (hr' : ∀ j, 0 ≤ r' j) (hother : ∀ k, k ≠ i → ∃ j, 0 < r k j)
    (p : Fin m → ℝ) (x : Fin n → Fin m → ℝ) (p' : Fin m → ℝ) (x' : Fin n → Fin m → ℝ)
    (hE : IsMarketEq I.B (linRep r) (orthant m) p x)
    (hE' : IsMarketEq I.B (linRep (Function.update r i r')) (orthant m) p' x') :
    ∑ j ∈ Finset.univ.filter (fun j => p j < p' j), p' j ≤
      I.B i + ∑ j ∈ Finset.univ.filter (fun j => p j < p' j), p j := by sorry

end TradingPostNSW.Leontief.Supplement
