-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TCPf_eq_of_cc
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.eq_of_cc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:29.108799+00:00
-- url     : https://prove2.me/theorems/41e674b4-85d5-4c24-b83f-fa3f737326f2
-- title:
--   TCPf: eq of cc
-- statement:
--   The TCPf construction uses the eq of cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L84-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/TaylorComp.lean#L84-L93

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
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.TCPf.eq_of_cc (F G : MvPowerSeries σ ℂ)
    (h : ∀ l : List σ, constantCoeff (l.foldr (fun q H => pderiv ℂ q H) F) =
      constantCoeff (l.foldr (fun q H => pderiv ℂ q H) G)) : F = G := by sorry
