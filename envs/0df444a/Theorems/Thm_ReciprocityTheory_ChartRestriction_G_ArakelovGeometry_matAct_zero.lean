-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_matAct_zero
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.matAct_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:43.543382+00:00
-- url     : https://prove2.me/theorems/6177ed0a-f0fd-5d00-b67c-6a810213faf7
-- title:
--   Arakelov Geometry: mat Act zero
-- statement:
--   The Arakelov Geometry construction uses the mat Act zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStA.lean#L46-L48

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
variable {J : Type} [Fintype J] [DecidableEq J]
variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.matAct_zero (A : Matrix J J ℚ) : matAct A (0 : J → Ω) = 0 := by sorry
