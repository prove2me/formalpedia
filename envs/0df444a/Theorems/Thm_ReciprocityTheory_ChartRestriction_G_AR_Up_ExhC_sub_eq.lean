-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ExhC_sub_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.sub_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:57:20.972176+00:00
-- url     : https://prove2.me/theorems/d22f2191-8aa3-5d51-8468-46b01750f34d
-- title:
--   Exh C: sub eq
-- statement:
--   The Exh C construction uses the sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfB.lean#L40-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExhaustStatementPfB.lean#L40-L76

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC
open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
variable {f p q N' : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC.sub_eq (a : ℝ) :
    {v : V (nD f p q + N') | v ∈ OmSet f p q N' ∧ eOm v ≤ a} =
      {v | (∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖tPart v‖ ^ 2) - a) ≤ ∏ k, dk (zPart v) k} := by sorry
