-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_inner_of_derivation
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.inner_of_derivation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:19.133173+00:00
-- url     : https://prove2.me/theorems/d621df27-8d0e-506b-b2b5-33b4f609e0d5
-- title:
--   Canon: inner of derivation
-- statement:
--   The Canon construction uses the inner of derivation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L16-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L16-L60

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

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.inner_of_derivation {O W : Type} [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] [AddCommGroup W]
    [Module ℚ W] (L R : O →+* Module.End ℚ W) (hc : ∀ a b, L a * R b = R b * L a) (D : O →+ W)
    (hD : ∀ a b, D (a * b) = R b (D a) + L a (D b)) : ∃ β : W, ∀ a, D a = R a β - L a β := by sorry
