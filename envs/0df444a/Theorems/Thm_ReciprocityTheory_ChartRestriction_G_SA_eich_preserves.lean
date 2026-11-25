-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_preserves
-- name    : ReciprocityTheory.ChartRestriction.G.SA.eich_preserves
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:35.022835+00:00
-- url     : https://prove2.me/theorems/4fdef3ce-52d1-44a3-82bd-73d61952c3b3
-- title:
--   SA: eich preserves
-- statement:
--   The SA construction uses the eich preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L153-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L153-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SAOpenStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichPreserves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.SA
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R] (σ : R →+* R)
  (J : Matrix ι ι R)
variable {σ J}
variable (hσ : ∀ x, σ (σ x) = x) (hJ : Jᵀ = J.map σ)
include hσ hJ

theorem ReciprocityTheory.ChartRestriction.G.SA.eich_preserves {e u : ι → R} {c : R} (he : hf σ J e e = 0) (hue : hf σ J u e = 0)
    (hc : c + σ c + hf σ J u u = 0) (x y : ι → R) :
    hf σ J (eich σ J e u c *ᵥ x) (eich σ J e u c *ᵥ y) = hf σ J x y := by sorry
