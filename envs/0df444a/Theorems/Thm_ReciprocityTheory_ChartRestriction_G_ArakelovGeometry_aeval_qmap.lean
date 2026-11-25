-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_qmap
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_qmap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:34.445811+00:00
-- url     : https://prove2.me/theorems/d33630dd-61cc-4063-b36a-388d765f3b44
-- title:
--   Arakelov Geometry: aeval qmap
-- statement:
--   The Arakelov Geometry construction uses the aeval qmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L86-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L86-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_HSClosing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {J : Type} [Fintype J] {Ω : Type*} [Field Ω] [CharZero Ω]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_qmap {S : Type*} [CommRing S] [Algebra ℚ S] (z : J → S) (f : MvPolynomial J ℤ) :
    aeval z (qmap f) = aeval z f := by sorry
