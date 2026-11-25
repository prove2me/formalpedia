-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isReduced_tensor_finite
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isReduced_tensor_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:10:04.012402+00:00
-- url     : https://prove2.me/theorems/b1209df5-df15-52b5-9697-3eab8cfa70f3
-- title:
--   Arakelov Geometry: is Reduced tensor finite
-- statement:
--   The Arakelov Geometry construction uses the is Reduced tensor finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L12-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Jacobson.Ring
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isReduced_tensor_finite (Ω E : Type*) [Field Ω] [CharZero Ω] [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : IsReduced (E ⊗[ℚ] Ω) := by sorry
