-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimA_perp_surj
-- name    : ReciprocityTheory.ChartRestriction.G.I2.DimA.perp_surj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:27:27.383584+00:00
-- url     : https://prove2.me/theorems/fbc06ab3-e1d9-4ff2-97d9-3c09a2b0d469
-- title:
--   Dim A: perp surj
-- statement:
--   The Dim A construction uses the perp surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PerpSurj.lean#L58-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PerpSurj.lean#L58-L72

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PerpSurj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.DimA
open Module
variable {H : Type*} [AddCommGroup H] (B : H →ₗ[ℤ] H →ₗ[ℤ] ℤ)
variable (halt : ∀ h, B h h = 0) (e f : H) (he : B e f = 1)
include halt he

theorem ReciprocityTheory.ChartRestriction.G.I2.DimA.perp_surj (hB : ∀ φ : H →ₗ[ℤ] ℤ, ∃ x, B x = φ) (φ : perp B e f →ₗ[ℤ] ℤ) :
    ∃ x : perp B e f, B.domRestrict₁₂ (perp B e f) (perp B e f) x = φ := by sorry
