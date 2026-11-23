-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_const
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptNs_const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:46.827483+00:00
-- url     : https://prove2.me/theorems/269f89d9-562a-48b9-bfae-79df2077ff5b
-- title:
--   Sh: pt Ns const
-- statement:
--   The Sh construction uses the pt Ns const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L19-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtSolveMapFixedIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_NsmulCoprimeBijectiveCurves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptNs_const (G : LogFGL v d) : ∀ n a, constantCoeff (ptNs G n a) = 0
  := by sorry
