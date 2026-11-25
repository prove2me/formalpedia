-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_mul_coeff_low_degree
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.taylor_mul_coeff_low_degree
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:20.598499+00:00
-- url     : https://prove2.me/theorems/1e9837dc-3469-4612-8f90-058eb62af2b0
-- title:
--   TM: taylor mul coeff low degree
-- statement:
--   The TM construction uses the taylor mul coeff low degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorMul.lean#L141-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorMul.lean#L141-L183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_Taylor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorMul
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TM
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TM.taylor_mul_coeff_low_degree (N : ℕ) : ∀ (f h : (Fin g → ℂ) → ℂ), ContDiffAt ℂ ω f 0 → ContDiffAt ℂ ω h 0 →
    ∀ n : Fin 1 × Fin g →₀ ℕ, n.degree < N → coeff n (tay (f * h) 0) = coeff n (tay f 0 * tay h 0) := by sorry
