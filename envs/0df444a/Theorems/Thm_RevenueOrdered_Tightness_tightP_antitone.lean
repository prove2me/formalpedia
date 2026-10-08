-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightP_antitone
-- name    : RevenueOrdered.Tightness.tightP_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:16:52.43366+00:00
-- url     : https://prove2.me/theorems/b493241d-be5d-4f17-aa75-9cb8c36cd7ba
-- title:
--   (7), p. 10 — product choice probabilities of the tight instance do not increase
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of the tight instance, with $0<\varepsilon\le\tfrac12$. Then
--   $$
--   \mathcal P((i,j),S)\ge\mathcal P((i,j),S')\quad\text{for every }S\subseteq S'\subseteq\mathcal C\text{ and }(i,j)\in S.
--   $$
--
--   This is the product case of the regularity axiom (iv). The paper says it "can be checked from the definition".
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4, inequality (7)

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- Inequality (7) (p. 10): in the tight instance,
`𝒫((i,j), S) ⩾ 𝒫((i,j), S')` for every `S ⊆ S' ⊆ 𝒞` and `(i,j) ∈ S`. -/
theorem tightP_antitone (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S S' : Finset (TightProduct k)) (hSS' : S ⊆ S') (x : TightProduct k) (hx : x ∈ S) :
    tightP k ε x S' ≤ tightP k ε x S := by sorry

end RevenueOrdered.Tightness
