-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_hf_add_left
-- name    : ReciprocityTheory.ChartRestriction.G.SA.hf_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:46.006948+00:00
-- url     : https://prove2.me/theorems/073b1436-3cfe-498d-a918-46688bb14b48
-- title:
--   SA: hf add left
-- statement:
--   The SA construction uses the hf add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L17-L21

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

theorem ReciprocityTheory.ChartRestriction.G.SA.hf_add_left (x x' y : ι → R) : hf σ J (x + x') y = hf σ J x y + hf σ J x' y := by sorry
