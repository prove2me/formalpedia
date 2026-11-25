-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_vmv_mulVec
-- name    : ReciprocityTheory.ChartRestriction.G.SA.vmv_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:34:40.992718+00:00
-- url     : https://prove2.me/theorems/0bac932f-191b-4934-a764-2a3106bd2c5a
-- title:
--   SA: vmv mul Vec
-- statement:
--   The SA construction uses the vmv mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/EichPreserves.lean#L126-L130

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

theorem ReciprocityTheory.ChartRestriction.G.SA.vmv_mulVec (u v w : ι → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by sorry
