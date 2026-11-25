-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_zero_mem_Hset
-- name    : ReciprocityTheory.ChartRestriction.G.TB.zero_mem_Hset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:22.107988+00:00
-- url     : https://prove2.me/theorems/033e6c27-baa0-4051-a5ab-f29638e0acda
-- title:
--   TB: zero mem Hset
-- statement:
--   The TB construction uses the zero mem Hset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ConnectionKillsSeries.lean#L133-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/ConnectionKillsSeries.lean#L133-L135

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem ReciprocityTheory.ChartRestriction.G.TB.zero_mem_Hset (h : PS ℚ 2 0) : (0 : (Fin 0 → ℚ) × (Fin 0 → ℚ)) ∈ Hset (R := ℤ) ℚ h := by sorry
