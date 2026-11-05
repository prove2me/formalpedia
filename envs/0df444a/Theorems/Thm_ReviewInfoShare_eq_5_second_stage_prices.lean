-- Prove2me | Theorems.Thm_ReviewInfoShare_eq_5_second_stage_prices
-- name    : ReviewInfoShare.eq_5_second_stage_prices
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:40:42.368227+00:00
-- url     : https://prove2.me/theorems/acd475d3-77b3-4f1d-8f2b-3581d22efd27
-- title:
--   (5) — unique second-stage wholesale-contract prices
-- statement:
--   Fix a quality $q$ with cost $c_q$. The second-stage game has an equilibrium, and in every equilibrium the prices are determined: for every platform estimate $t$ and belief $z$, with information sharing the manufacturer prices on $t$ and
--   $$
--   (p_2^*,w_2^*)=\Bigl(\tfrac14(3\alpha+3tz+c_q),\ \tfrac12(\alpha+tz+c_q)\Bigr),
--   $$
--   and without sharing it prices on $\mu_\theta$ and
--   $$
--   (p_2^*,w_2^*)=\Bigl(\tfrac14(3\alpha+(2t+\mu_\theta)z+c_q),\ \tfrac12(\alpha+\mu_\theta z+c_q)\Bigr).
--   $$
--   On the path $t=\hat\theta$ and $z=\hat q_2$. These are the prices that every profit formula of the wholesale contract rests on.
--
--   **Formalization Note** The statement is pointwise in $(t,z)$ and needs no probability.
--
--   Differences from the source:
--   - generalization: π(q̄) < π(q̲), assumed throughout the paper (p.16), and the data assumptions of pp.9–16 → none; reason: the pointwise optimization uses none of them, so the statement specializes to the printed setting
--   - reading: plain c in (5) and on p.14 → c_q; reason: a plain c is neither cost symbol, and the second-stage profit on p.14 uses c_q
--   - reading: without sharing, w₂* = arg max (w − c)(α + µ_θ q̂₂ − p₂(w)) with p₂(w) containing θ̂ → p₂(w) evaluated at µ_θ in place of θ̂; reason: the manufacturer does not observe θ̂, and this reading gives (5)
--   - encoding: the equilibrium prices of the subgame perfect solution (p.14), found by backward induction → every profile of price functions optimal at each wholesale price and each (t, z), with t, z the realized estimate and belief on the path; reason: subgame perfection at every information state; this optimality determines the path prices, so no instance changes
-- source:
--   Shin–Zeevi, Product Quality and Information Sharing in the Presence of Reviews, SSRN 3886954, (5), p.14

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Wholesale

namespace ReviewInfoShare

/-- Shin–Zeevi, *Product Quality and Information Sharing in the Presence of Reviews*, SSRN 3886954,
(5), p.14. The second-stage equilibrium exists and its prices are unique: with sharing
`(p₂*, w₂*) = (¼(3α + 3θ̂q̂₂ + c), ½(α + θ̂q̂₂ + c))`, and without sharing
`(p₂*, w₂*) = (¼(3α + (2θ̂ + µ_θ)q̂₂ + c), ½(α + µ_θ q̂₂ + c))`.

**Formalization Note.** Stated pointwise in the platform's estimate `t` (`= θ̂`) and the belief `z`
(`= q̂₂`). The plain `c` of (5) is `c_q`. Without sharing the manufacturer's estimate is `µ_θ`. -/
theorem eq_5_second_stage_prices (P : Params) (q : Quality) :
    (∃ p₂ w₂, IsWholesaleStage2Eq P q p₂ w₂) ∧
    ∀ p₂ w₂, IsWholesaleStage2Eq P q p₂ w₂ → ∀ t z : ℝ,
      (p₂ (w₂ t z) t z = (3 * P.α + 3 * t * z + P.cost q) / 4 ∧
        w₂ t z = (P.α + t * z + P.cost q) / 2) ∧
      (p₂ (w₂ P.μ z) t z = (3 * P.α + (2 * t + P.μ) * z + P.cost q) / 4 ∧
        w₂ P.μ z = (P.α + P.μ * z + P.cost q) / 2) := by sorry

end ReviewInfoShare
