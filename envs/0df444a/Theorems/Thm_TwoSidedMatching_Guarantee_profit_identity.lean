-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_profit_identity
-- name    : TwoSidedMatching.Guarantee.profit_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:07.995707+00:00
-- url     : https://prove2.me/theorems/6afb308e-60d2-4a0e-980c-abb47e14314f
-- title:
--   Supplemental Note p. 13 — policy profit identity
-- statement:
--   Under waiting-adjusted fixed prices, myopic requests and greedy matching, expected profit equals the fixed spread times the expected number of matched pairs minus accumulated imbalance waiting cost:
--
--   $$J^{\pi^{\mathrm{WFP}},M^g}=(p^*-w^*)\mathbb E[\min\{N^d_T,N^s_T\}]-\int_0^T\mathbb E\left[b(N^d_t-N^s_t)^++h(N^s_t-N^d_t)^+\right]dt.$$
--
--   This is the compensation identity at the center of the performance calculation.
--
--   **Formalization Note** Profit is independently defined from expected posted-price receipts less payments. Integrability of profit and the time-integrated waiting term is part of the conclusion.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 13, proof of Theorem 2 (PDF p. 53)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

open MeasureTheory

namespace TwoSidedMatching.Guarantee

/-- Supplemental Note p. 13, the first and eighth lines of the proof of Theorem 2. -/
theorem profit_identity (E : Environment) (lamD lamS T b h : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS < E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T)
    (hb : 0 ≤ b) (hh : 0 ≤ h) :
    Integrable (profit E lamD lamS T b h) (P E lamD lamS T) ∧
    IntervalIntegrable
      (fun t => ∫ ω,
        (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
          h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0)
        ∂P E lamD lamS T) volume 0 T ∧
    policyProfit E lamD lamS T b h =
      (pStar E lamD lamS T - wStar E lamD lamS T) *
        (∫ ω, (min (Nd E lamD lamS T ω T) (Ns E lamD lamS T ω T) : ℝ)
          ∂P E lamD lamS T) -
        (∫ t in (0 : ℝ)..T, ∫ ω,
          (b * max ((Nd E lamD lamS T ω t : ℝ) - (Ns E lamD lamS T ω t : ℝ)) 0 +
            h * max ((Ns E lamD lamS T ω t : ℝ) - (Nd E lamD lamS T ω t : ℝ)) 0)
          ∂P E lamD lamS T) := by sorry

end TwoSidedMatching.Guarantee
