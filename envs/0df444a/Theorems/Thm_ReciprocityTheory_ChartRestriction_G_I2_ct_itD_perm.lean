-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_ct_itD_perm
-- name    : ReciprocityTheory.ChartRestriction.G.I2.ct_itD_perm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:29:01.582619+00:00
-- url     : https://prove2.me/theorems/0ecef714-65df-44c5-b1dd-a7b4b9efe9ba
-- title:
--   I2: ct it D perm
-- statement:
--   The I2 construction uses the ct it D perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L164-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColTorusA.lean#L164-L185

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
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem ReciprocityTheory.ChartRestriction.G.I2.ct_itD_perm {f : W → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) {l₁ l₂ : List W} (h : l₁.Perm l₂) :
    (fun y => itD f l₁ y) = fun y => itD f l₂ y := by sorry
