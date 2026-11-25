-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ringKrullDim_mvPoly_fin_int
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ringKrullDim_mvPoly_fin_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:09:56.449261+00:00
-- url     : https://prove2.me/theorems/fd099c8a-b576-5cfb-9dd2-cc42471977f1
-- title:
--   Arakelov Geometry: ring Krull Dim mv Poly fin int
-- statement:
--   The Arakelov Geometry construction uses the ring Krull Dim mv Poly fin int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/StepTStB.lean#L118-L122

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemSec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_StepTStB
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
variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ringKrullDim_mvPoly_fin_int :
    ringKrullDim (MvPolynomial (Fin (D + 1)) ℤ) = ((D + 2 : ℕ) : WithBot ℕ∞) := by sorry
