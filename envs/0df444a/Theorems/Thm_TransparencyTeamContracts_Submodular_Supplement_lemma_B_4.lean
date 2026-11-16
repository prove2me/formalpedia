-- Prove2me | Theorems.Thm_TransparencyTeamContracts_Submodular_Supplement_lemma_B_4
-- name    : TransparencyTeamContracts.Submodular.Supplement.lemma_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:20:55.053597+00:00
-- url     : https://prove2.me/theorems/31b68a0f-853c-42a6-915c-0be30c389cc6
-- title:
--   Lemma B.4 (used in the proof of Theorem B.1) — Fixed-cost two-state attainment
-- statement:
--   Fix $0<c<1$. There exist $p_0\in[0,1]$ with $\ell_c(p_0)\le1$ and $q\in[0,1]$ such that the two-state prior on $(0,1)$ and $(p_0,\ell_c(p_0))$, with masses $q$ and $1-q$, has positive full-disclosure payoff and attains the largest no/full-disclosure ratio over every finite single-agent setting at this same cost:
--   $$\frac{U_P^N(D)}{U_P^F(D)}\le\frac{U_P^N(D^\star)}{U_P^F(D^\star)}\qquad(U_P^F(D)>0).$$
--   The conclusion supplies the actual two-state model and prior, fixes their technologies and costs, and identifies their full and no-information values with the derived two-point expressions. Those expressions use the base stateless optimum, so attainment is about the operational contract problem rather than an assumed scalar formula.
--
--   Differences from the source:
--   - encoding: finite agents and states with real data and operational optimal utilities → Fin indices and the published base game, simplex prior and operational suprema; reason: finite relabeling preserves every source instance; nonempty bounded payoff sets give the same optimal values, with no zero-cost or positive-baseline restriction
--   - encoding: the supremum at each fixed c is achieved by a two-point prior → a positive-denominator two-state witness and a universal ratio upper bound over all finite models at that same c; reason: the witness lies in the compared family, so the universal bound states attainment, not just equality of two suprema; the source excludes zero denominators on printed p.26
-- source:
--   Paul Duetting, Yingkai Li, Inbal Talgam-Cohen, Jinzhao Wu, STOC 2027 submission #1292 (October 2026), Lemma B.4, printed p. 27 (PDF p. 29)

import Mathlib
import Definitions.Def_TransparencyTeamContracts_Submodular_Supplement_SingleAgent

open Finset

namespace TransparencyTeamContracts.Submodular.Supplement

/-- Lemma B.4, printed 27 / PDF 29, fixed cost and actual attainment. -/
theorem lemma_B_4 (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    ∃ (p₀ q : ℝ), 0 ≤ p₀ ∧ p₀ ≤ 1 ∧ cutoff c p₀ ≤ 1 ∧ 0 ≤ q ∧ q ≤ 1 ∧
      0 < twoPointFull c p₀ q ∧
      (∃ (M : Model 1 2) (D : Belief 2),
        (∀ i, M.c i = c) ∧ M.f 0 = singleReward 0 1 ∧
        M.f 1 = singleReward p₀ (cutoff c p₀) ∧
        (D : Fin 2 → ℝ) 0 = q ∧ (D : Fin 2 → ℝ) 1 = 1 - q ∧
        fullInformation M D = twoPointFull c p₀ q ∧ noInformation M D = twoPointNo c p₀ q) ∧
      (∀ (m : ℕ) (M : Model 1 m) (D : Belief m),
        (∀ i, M.c i = c) → 0 < fullInformation M D →
        noInformation M D / fullInformation M D ≤ twoPointNo c p₀ q / twoPointFull c p₀ q) := by sorry

end TransparencyTeamContracts.Submodular.Supplement
