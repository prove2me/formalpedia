-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_partA
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:22.301859+00:00
-- url     : https://prove2.me/theorems/92a58604-151d-56f4-8ff8-7ef094aee997
-- title:
--   TCPf: part A
-- statement:
--   The TCPf construction uses the part A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L290-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L290-L319

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_TaylorComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_TaylorComp
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.PullbackSections
open scoped ContDiff Topology
variable {g : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.partA (f : (Fin g → ℂ) → ℂ) (hf : ContDiffAt ℂ ω f 0) (c : Fin g → ℂ) :
    tay (fun z => f fun i => c i * z i) 0 = subst (fun p : Fin 1 × Fin g => C (c p.2) * X p) (tay f 0) := by sorry
