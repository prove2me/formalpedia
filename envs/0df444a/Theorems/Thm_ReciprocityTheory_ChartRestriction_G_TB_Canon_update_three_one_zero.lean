-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_update_three_one_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.update_three_one_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:03.860018+00:00
-- url     : https://prove2.me/theorems/6dbf4ea5-ad36-56a4-a748-8a6072a01656
-- title:
--   Canon: update three one zero
-- statement:
--   The Canon construction uses the update three one zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L320-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L320-L322

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.Pi
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.LocalProperties.Reduced
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CanonA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries TensorProduct
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Canon
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] {d : ℕ}
variable {n l : ℕ}
variable [Algebra ℚ k]

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.update_three_one_zero : (Function.update gen 1 0 : Fin 3 → Q k d 3) = ![gen 0, 0, gen 2] := by sorry
