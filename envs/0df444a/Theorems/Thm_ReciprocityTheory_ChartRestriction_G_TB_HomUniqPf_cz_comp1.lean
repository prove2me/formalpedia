-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_HomUniqPf_cz_comp1
-- name    : ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf.cz_comp1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:50.864926+00:00
-- url     : https://prove2.me/theorems/a595adde-821d-44a0-a952-c1e6b7eadb90
-- title:
--   Hom Uniq Pf: cz comp1
-- statement:
--   The Hom Uniq Pf construction uses the cz comp1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HomUniq.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/HomUniq.lean#L56-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConstantCoeffEv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
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
open ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf
open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux
variable {k : Type} [CommRing k] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.HomUniqPf.cz_comp1 {n : ℕ} (φ : Pt k 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (a : Pt k n d)
    (ha : ∀ i, constantCoeff (a i) = 0) : ∀ i, constantCoeff (comp1 φ a i) = 0 := by sorry
