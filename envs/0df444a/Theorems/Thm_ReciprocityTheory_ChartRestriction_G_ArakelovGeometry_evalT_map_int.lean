-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_evalT_map_int
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.evalT_map_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:05:46.305845+00:00
-- url     : https://prove2.me/theorems/f35b340f-5911-534e-a2fa-a1dda39f7513
-- title:
--   Arakelov Geometry: eval T map int
-- statement:
--   The Arakelov Geometry construction uses the eval T map int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L118-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/ABridgeStB.lean#L118-L124

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
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.evalT_map_int (x : J → Ω) (f : MvPolynomial J ℤ) :
    evalT x (map (Int.castRingHom ℂ) f) = (1 : ℂ) ⊗ₜ[ℚ] aeval x f := by sorry
