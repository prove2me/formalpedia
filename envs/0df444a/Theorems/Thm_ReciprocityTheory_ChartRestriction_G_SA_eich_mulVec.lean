-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_eich_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.SA.eich_mulVec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:53.818641+00:00
-- url     : https://prove2.me/theorems/a6896a40-bf6b-4c9d-8c69-e16b6fa2c95f
-- title:
--   SA: eich mul Vec
-- statement:
--   The SA construction uses the eich mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L134-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L134-L137

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
variable (σ J)

theorem ReciprocityTheory.ChartRestriction.G.SA.eich_mulVec (e u : ι → R) (c : R) (x : ι → R) :
    eich σ J e u c *ᵥ x = x + hf σ J x e • u - hf σ J x u • e + (c * hf σ J x e) • e := by sorry
