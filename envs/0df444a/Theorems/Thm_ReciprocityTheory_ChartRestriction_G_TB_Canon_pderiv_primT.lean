-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Canon_pderiv_primT
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_primT
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:35.06281+00:00
-- url     : https://prove2.me/theorems/c372cc5a-50d6-42bf-b2c2-05021eb097f6
-- title:
--   Canon: pderiv prim T
-- statement:
--   The Canon construction uses the pderiv prim T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L69-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CanonA.lean#L69-L118

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
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [DecidableEq τ]

theorem ReciprocityTheory.ChartRestriction.G.TB.Canon.pderiv_primT (T : Finset τ) (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a ∈ T, ∀ c ∈ T, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) (hv : v ∈ T) : pderiv k v (primT T ω) = ω v := by sorry
