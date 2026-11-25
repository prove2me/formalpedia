-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_iter_mul_jet_one
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_iter_mul_jet_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:28:56.682127+00:00
-- url     : https://prove2.me/theorems/bb5d45df-4787-4716-9946-09bac1a25329
-- title:
--   I2: ct iter mul jet one
-- statement:
--   The I2 construction uses the ct iter mul jet one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L90-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L90-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColTorusA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open Complex

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_iter_mul_jet_one {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f g : V → ℂ) (hf : ContDiff ℂ (⊤ : ℕ∞) f) (hg : ContDiff ℂ (⊤ : ℕ∞) g) (c : ℕ)
    (h0 : g 0 = 1) (hjet : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j g 0 = 0) :
    iteratedFDeriv ℂ c (fun v => f v * g v) 0 = iteratedFDeriv ℂ c f 0 := by sorry
