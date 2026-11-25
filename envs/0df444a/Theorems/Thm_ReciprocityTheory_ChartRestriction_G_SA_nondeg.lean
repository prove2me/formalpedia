-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_nondeg
-- name    : ReciprocityTheory.ChartRestriction.G.SA.nondeg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:08.292321+00:00
-- url     : https://prove2.me/theorems/a3f73356-72d6-4947-99a1-85f059056488
-- title:
--   SA: nondeg
-- statement:
--   The SA construction uses the nondeg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L29-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/StrongApproximation/SubProjOrth.lean#L29-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_EichAlongSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_StrongApproximation_SubProjOrth
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] {σ : K →+* K}
  {J : Matrix ι ι K}

theorem ReciprocityTheory.ChartRestriction.G.SA.nondeg (hdet : IsUnit J.det) {x : ι → K} (h : ∀ z, hf σ J x z = 0) : x = 0 := by sorry
