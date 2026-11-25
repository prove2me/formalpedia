-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_zero_of_add
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.zero_of_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:40:10.886811+00:00
-- url     : https://prove2.me/theorems/54ab58f3-4707-5493-9eb9-70e5f18d21bc
-- title:
--   Canon: zero of add
-- statement:
--   The Canon construction uses the zero of add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L496-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L496-L522

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

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.zero_of_add (f : PS k 3 d) (add : ∀ {n} (x y v v' : Q k d n), E3 f x y (v + v') = E3 f x y v + E3 f x y v')
    (h : ∀ {n} b (x y : Q k d n), E3 (pderiv k (2, b) f) x y 0 = 0) : f = 0 := by sorry
