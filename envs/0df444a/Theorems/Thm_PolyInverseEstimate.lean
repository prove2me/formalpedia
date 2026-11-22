-- Prove2me | Theorems.Thm_PolyInverseEstimate
-- name    : PolyInverseEstimate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:17:16.361396+00:00
-- url     : https://prove2.me/theorems/f15901ef-873e-4c9d-83d9-5fa1b96f8166
-- title:
--   Poly Inverse Estimate: Poly Inverse Estimate
-- statement:
--   The Poly Inverse Estimate construction uses the Poly Inverse Estimate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PolyInverseEstimate.lean#L4-L200
-- source:
--   https://github.com/na0b/phigherorder-lean/blob/1ab3890a96c86ab99822d51d99058a81269c2262/PHigherOrder/PolyInverseEstimate.lean#L4-L200

import Definitions.Def_PHigherOrder_PolyDiagonalJetRigidity
import Definitions.Def_PHigherOrder_VanishingOnUnitBallKillsJets
import Definitions.Def_PHigherOrder_PolyInverseEstimate
import Theorems.Thm_PolyDiagonalJetRigidity
import Theorems.Thm_VanishingOnUnitBallKillsJets

set_option autoImplicit false

theorem PolyInverseEstimate (k : ℕ) :
    ∃ Ck : ℝ, 0 < Ck ∧ ∀ R : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) R →
      (∀ x : Plane, iteratedFDeriv ℝ (k + 1) R x = 0) →
      ∀ (z : Plane) (d A : ℝ), 0 < d → 0 ≤ A →
      (∀ y ∈ Metric.ball z d, |R y| ≤ A) →
      ‖iteratedFDeriv ℝ k R z‖ ≤ Ck * A / d ^ k := by sorry
