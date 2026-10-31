-- Prove2me | Theorems.Thm_SlottingFees_lemma_2
-- name    : SlottingFees.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:38.416135+00:00
-- url     : https://prove2.me/theorems/91354ea5-9568-4065-9a04-2e2b9c7cdb57
-- title:
--   Lemma 2 — participation and wholesale prices when $|A|=1$
-- statement:
--   Consider the low-variety subgame under the standing assumptions, with any optimal stage-3 pricing strategy. Let $v_i\ge v_j$ ($j\neq i$), where $i$ is manufacturer 1 if $v_i=v_j$.
--
--   1. If $0\le S\le v_j/8$, both manufacturers participate. Manufacturer $j$ offers its zero-profit price
--   $$
--   \tilde w_j(S)=c_j+\frac{\sqrt{q_j}}{2}\Bigl(\sqrt{v_j}-\sqrt{v_j-8S}\Bigr),
--   $$
--   and manufacturer $i$ enters the assortment at
--   $$
--   \tilde w_i(S)=\min\Bigl\{\frac{q_i+c_i}{2},\ q_i-\frac{\sqrt{q_i}}{2}\Bigl(\sqrt{v_j}+\sqrt{v_j-8S}\Bigr)\Bigr\}.
--   $$
--   2. If $v_j/8<S\le v_i/8$, only manufacturer $i$ participates, and it sets $\tilde w_i(S)=(q_i+c_i)/2$.
--
--   In both cases a stage-2 outcome of the formulation (5)–(8) exists, and every outcome is the one described.
--
--   This lemma gives the stage-2 response to the slotting fee that the retailer optimizes in Corollary 1 and Proposition 1.
--
--   Differences from the source:
--   - reading: 'without loss of generality, suppose v_i ≥ v_j' → v_j < v_i, or v_i = v_j with i = manufacturer 1; reason: at a tie the formulation's entrant rule makes manufacturer 1 the entrant, and the displayed w̃_i is the entrant's price
--   - reading: the |A| = 1 stage 2 of (5)-(8): the manufacturer that cannot enter offers its zero-profit price, the other solves (6)-(7) → IsStage2Outcome1: zero-profit price = least w ≥ c_l with non-negative profit; the entrant is the manufacturer whose zero-profit price gives the retailer the larger optimal gross profit, ties to manufacturer 1; (7) as the primitive condition that the retailer weakly prefers the entrant; reason: the paper does not say which manufacturer enters; this is its own logic (p.11) and makes the entrant the more attractive manufacturer of Lemma 2; (7) is equivalent to its closed form by Lemma 1
--   - encoding: 'both manufacturers participate' / 'only manufacturer i participates' → both (resp. only i) can afford S: some w ≥ c_l gives non-negative profit; reason: the paper's participation rule (p.9: a manufacturer participates if it can afford the slotting fee)
--   - encoding: the manufacturers' decisions are as displayed → a stage-2 outcome exists and every outcome carries i at w̃_i(S); j's zero-profit price is w̃_j(S); reason: makes existence explicit and rules out a vacuous statement
--   - encoding: products 1 and 2; Pr over θ ~ U[0,1] → indices 0 and 1 of Fin 2; Lebesgue measure of the set of types in [0,1], as a real number; reason: Lean convention; same instances
-- source:
--   Alan–Kurtuluş–Nakkas, Retail Category Management with Slotting Fees, MSOM (2024), doi:10.1287/msom.2022.0143, Lemma 2, pp.11–12

import Mathlib
import Definitions.Def_SlottingFees_ClosedForms
import Definitions.Def_SlottingFees_Subgame1

namespace SlottingFees

/-- **Lemma 2**, pp.11–12 (Alan, Kurtuluş, Nakkas, MSOM 2024, doi:10.1287/msom.2022.0143):
participation and wholesale prices when `|A| = 1`.

Under the standing assumptions, for every optimal stage-3 pricing strategy, let `v_i ≥ v_j`
(`j ≠ i`), with `i` = manufacturer 1 when `v_i = v_j`. Then:

* (i) if `0 ≤ S ≤ v_j/8`, both manufacturers can afford `S`; manufacturer `j`'s zero-profit price
  is `w̃_j(S) = c_j + (√q_j/2)(√v_j − √(v_j − 8S))`; a stage-2 outcome exists, and in every one
  manufacturer `i` enters at
  `w̃_i(S) = min{(q_i + c_i)/2, q_i − (√q_i/2)(√v_j + √(v_j − 8S))}`;
* (ii) if `v_j/8 < S ≤ v_i/8`, only manufacturer `i` can afford `S`; a stage-2 outcome exists, and
  in every one manufacturer `i` is carried at `w̃_i(S) = (q_i + c_i)/2`.

**Formalization Note** The stage-2 outcome is the paper's formulation (5)–(8)
(`IsStage2Outcome1`). At `v_i = v_j` the entrant is manufacturer 1 by the tie rule of
`IsStage2Outcome1`, so the lemma's "without loss of generality" is stated with that labelling.
Product 1 is `0`. -/
theorem lemma_2 (ω : Params) (hω : ω.Standing) (σ : Fin 2 → ℝ → ℝ) (hσ : IsOptPricing1 ω σ)
    (i : Fin 2) (hv : ω.v (other i) < ω.v i ∨ (ω.v (other i) = ω.v i ∧ i = 0)) (S : ℝ) :
    (0 ≤ S → S ≤ ω.v (other i) / 8 →
      CanAfford ω σ i S ∧ CanAfford ω σ (other i) S ∧
      IsZeroProfitPrice ω σ (other i) S
        (ω.c (other i) + Real.sqrt (ω.q (other i)) / 2 *
          (Real.sqrt (ω.v (other i)) - Real.sqrt (ω.v (other i) - 8 * S))) ∧
      (∃ o, IsStage2Outcome1 ω σ S o) ∧
      ∀ o, IsStage2Outcome1 ω σ S o →
        o = some (i, min ((ω.q i + ω.c i) / 2)
          (ω.q i - Real.sqrt (ω.q i) / 2 *
            (Real.sqrt (ω.v (other i)) + Real.sqrt (ω.v (other i) - 8 * S))))) ∧
    (ω.v (other i) / 8 < S → S ≤ ω.v i / 8 →
      CanAfford ω σ i S ∧ ¬ CanAfford ω σ (other i) S ∧
      (∃ o, IsStage2Outcome1 ω σ S o) ∧
      ∀ o, IsStage2Outcome1 ω σ S o → o = some (i, (ω.q i + ω.c i) / 2)) := by sorry

end SlottingFees
