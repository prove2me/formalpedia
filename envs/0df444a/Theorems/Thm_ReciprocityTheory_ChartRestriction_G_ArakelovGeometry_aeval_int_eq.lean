-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_int_eq
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_int_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:02:07.604684+00:00
-- url     : https://prove2.me/theorems/54798195-3f9e-561f-9d63-aee4ef79f5b9
-- title:
--   Arakelov Geometry: aeval int eq
-- statement:
--   The Arakelov Geometry construction uses the aeval int eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L82-L84

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

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.aeval_int_eq (z : J → ℂ) (f : MvPolynomial J ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by sorry
