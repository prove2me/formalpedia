-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_fct_add_single
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.fct_add_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:33:02.505035+00:00
-- url     : https://prove2.me/theorems/3a29138b-debd-568b-aa4f-cdd3bfc3cfb7
-- title:
--   Pullback Sections: fct add single
-- statement:
--   The Pullback Sections construction uses the fct add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L160-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/Taylor.lean#L160-L172

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped ContDiff
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.fct_add_single (n : Fin 1 × Fin g →₀ ℕ) (p : Fin 1 × Fin g) :
    fct (n + Finsupp.single p 1) = fct n * ((n p : ℂ) + 1) := by sorry
