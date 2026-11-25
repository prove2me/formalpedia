-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_G2_cc_T_q
-- name    : ReciprocityTheory.ChartRestriction.G.TB.G2.cc_T_q
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:41:16.147293+00:00
-- url     : https://prove2.me/theorems/93d7090c-a201-4453-b4e6-883a2061195a
-- title:
--   G2: cc T q
-- statement:
--   The G2 construction uses the cc T q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CcTMulQ.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/CcTMulQ.lean#L41-L50

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofListSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CcTMulQ
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
variable {ι : Type} (c : ι → ι → k)
variable (F : Fin d → PS k 2 d) (u : ι → Fin d → k) (q : PS k 1 d)
  (hq0 : constantCoeff q = 0) (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
  (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l'))
include hq2
include hq0 hq1

theorem ReciprocityTheory.ChartRestriction.G.TB.G2.cc_T_q (b : List ι) : constantCoeff (T F u b q) = ev2 c b := by sorry
