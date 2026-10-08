-- Prove2me | Theorems.Thm_RevenueOrdered_Tightness_tightP_sum_le_one
-- name    : RevenueOrdered.Tightness.tightP_sum_le_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:16:59.385092+00:00
-- url     : https://prove2.me/theorems/60799a40-19d5-46fe-91b2-a8aae452d88b
-- title:
--   Theorem 3.4 proof, p. 10 — axiom (iii) holds for the tight instance
-- statement:
--   Let $\mathcal P$ be the system of choice probabilities of the tight instance, with $0<\varepsilon\le\tfrac12$. For every $S\subseteq\mathcal C$,
--   $$
--   \sum_{(i,j)\in S}\mathcal P((i,j),S)\le\varepsilon^1+\varepsilon^2+\dots+\varepsilon^k<\frac{1}{1-\varepsilon}-1=\frac{\varepsilon}{1-\varepsilon}\le 1 .
--   $$
--
--   This is axiom (iii) for the instance.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 10, proof of Theorem 3.4 (display before (7))

import Mathlib
import Definitions.Def_RevenueOrdered_Tightness_ChoiceModel
import Definitions.Def_RevenueOrdered_Tightness_RevenueOrdered
import Definitions.Def_RevenueOrdered_Tightness_TightInstance

namespace RevenueOrdered.Tightness

/-- Axiom (iii) for the tight instance (p. 10): for every `S ⊆ 𝒞`,
`∑_{(i,j) ∈ S} 𝒫((i,j), S) ⩽ ε^1 + ⋯ + ε^k < 1/(1-ε) - 1 = ε/(1-ε) ⩽ 1`. -/
theorem tightP_sum_le_one (k : ℕ) (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (S : Finset (TightProduct k)) :
    ∑ x ∈ S, tightP k ε x S ≤ ∑ i ∈ Finset.Icc 1 k, ε ^ i ∧
      ∑ i ∈ Finset.Icc 1 k, ε ^ i < 1 / (1 - ε) - 1 ∧
      1 / (1 - ε) - 1 = ε / (1 - ε) ∧
      ε / (1 - ε) ≤ 1 := by sorry

end RevenueOrdered.Tightness
