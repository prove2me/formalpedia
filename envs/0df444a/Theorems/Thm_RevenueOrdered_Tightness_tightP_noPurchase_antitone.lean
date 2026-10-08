-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightP_noPurchase_antitone
-- name    : RevenueOrdered.Tightness.tightP_noPurchase_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:18:08.712061+00:00
-- url     : https://prove2.me/theorems/8252f3ef-d807-4d9f-83d3-1b2dbbc7c5eb
-- title:
--   (9), p. 10 — the no-purchase probability of the tight instance does not increase
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of the tight instance, with $0<\varepsilon\le\tfrac12$, and $\mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S)$. Then
--   $$
--   \mathcal P(0,S)\ge\mathcal P(0,S')\quad\text{for every }S\subseteq S'\subseteq\mathcal C .
--   $$
--
--   This is the no-purchase case of the regularity axiom (iv); the paper derives it from (8).
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4, inequality (9)

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- Inequality (9) (p. 10): in the tight instance, `𝒫(0, S) ⩾ 𝒫(0, S')` for every
`S ⊆ S' ⊆ 𝒞`, where `𝒫(0, S) = 1 - ∑_{x ∈ S} 𝒫(x, S)`. -/
theorem tightP_noPurchase_antitone (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') :
    RevenueOrdered.Ratio.noPurchase (tightP k ε) S' ≤ RevenueOrdered.Ratio.noPurchase (tightP k ε) S := by sorry

end RevenueOrdered.Tightness
