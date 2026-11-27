-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_exists_prim
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.exists_prim
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:25:50.68645+00:00
-- url     : https://prove2.me/theorems/996f780e-63cd-4d31-9fae-19f0e638c271
-- title:
--   Log Pf: exists prim
-- statement:
--   The Log Pf construction uses the exists prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogPoinc.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogPoinc.lean#L78-L80

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogPoinc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
variable {k : Type} [CommRing k] [Algebra ℚ k] {τ : Type} [Fintype τ] [DecidableEq τ]

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.exists_prim (ω : τ → MvPowerSeries τ k) (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) :
    ∃ ℓ : MvPowerSeries τ k, constantCoeff ℓ = 0 ∧ ∀ v, pderiv k v ℓ = ω v := by sorry
