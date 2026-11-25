-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pderiv_prim
-- name    : ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:52:20.615281+00:00
-- url     : https://prove2.me/theorems/6fb8885b-f9d4-4c95-b48e-f6181c457b14
-- title:
--   Log Pf: pderiv prim
-- statement:
--   The Log Pf construction uses the pderiv prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogPoinc.lean#L30-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/LogPoinc.lean#L30-L76

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

theorem ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_prim (ω : τ → MvPowerSeries τ k)
    (hω : ∀ a c, pderiv k c (ω a) = pderiv k a (ω c)) (v : τ) : pderiv k v (prim ω) = ω v := by sorry
