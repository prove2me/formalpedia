-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hx4v2_eq_ratio_smul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.hx4v2_eq_ratio_smul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:38:20.370871+00:00
-- url     : https://prove2.me/theorems/18258199-4b17-4bb0-b22d-b42542060592
-- title:
--   T0: hx4v2 eq ratio smul
-- statement:
--   The T0 construction uses the hx4v2 eq ratio smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormGenericRatioSpec.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/NormGenericRatioSpec.lean#L14-L22

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BasisBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormGenericRatioSpec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField

theorem ReciprocityTheory.ChartRestriction.G.T0.hx4v2_eq_ratio_smul {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V]
    (W : Submodule Ω V) (hW : Module.finrank Ω W = 1) {f g : V} (hf : f ∈ W) (hgW : g ∈ W)
    (hg : g ≠ 0) : f = ratio (Ω := Ω) f g • g := by sorry
