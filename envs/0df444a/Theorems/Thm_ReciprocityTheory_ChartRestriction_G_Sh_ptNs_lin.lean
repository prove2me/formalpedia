-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptNs_lin
-- name    : ReciprocityTheory.ChartRestriction.G.Sh.ptNs_lin
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:28.582714+00:00
-- url     : https://prove2.me/theorems/82d37c7c-261f-5528-971f-674d4aefc7ca
-- title:
--   Sh: pt Ns lin
-- statement:
--   The Sh construction uses the pt Ns lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/WeightedSumBounds/NsmulCoprimeBijectiveCurves.lean#L44-L58

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

theorem ReciprocityTheory.ChartRestriction.G.Sh.ptNs_lin (G : LogFGL v d) : ∀ (n : ℕ) (a s : Fin d),
    coeff (Finsupp.single s 1) (ptNs G n a) = if s = a then (n : C) else 0
  := by sorry
