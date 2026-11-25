-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_RgD_block
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.RgD.block
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:16.547805+00:00
-- url     : https://prove2.me/theorems/e0d2e0b0-4f02-5e4f-b523-05237bc7d04d
-- title:
--   Rg D: block
-- statement:
--   The Rg D construction uses the block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfB.lean#L95-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/RhGradStatementPfB.lean#L95-L154

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgD
open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.RgC
variable {f p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.RgD.block (hm : 0 < min p q) {v0 : V (nD f p q)} (hv0 : v0 ∈ Dset f p q) (k : Fin f) :
    ∃ Q : V (nD f p q) → ℝ, ContDiff ℝ ∞ Q ∧
      (∀ ξ, (leviV (nD f p q) (fun y => (Q y : ℂ)) v0 ξ).re ≤ 0) ∧
      Q v0 = (min p q : ℕ) ∧
      ∀ v ∈ Dset f p q, dk v k ^ (((min p q : ℕ) : ℝ)⁻¹) ≤
        dk v0 k ^ (((min p q : ℕ) : ℝ)⁻¹) * (Q v / (min p q : ℕ)) := by sorry
