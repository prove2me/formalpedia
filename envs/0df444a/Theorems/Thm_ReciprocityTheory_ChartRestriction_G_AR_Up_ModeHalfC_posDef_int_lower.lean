-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_ModeHalfC_posDef_int_lower
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.posDef_int_lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:02:38.218594+00:00
-- url     : https://prove2.me/theorems/3821f0b4-c83c-41e6-bafa-4fc3260c657c
-- title:
--   Mode Half C: pos Def int lower
-- statement:
--   The Mode Half C construction uses the pos Def int lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfC.lean#L13-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ModeHalfStatementPfC.lean#L13-L55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianLatticeMaps
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ModeHalfStatementPfC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC
open Matrix NumberField Complex ReciprocityTheory.ChartRestriction.G.FD Topology Filter ModeHalfA ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates Module
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.ModeHalfC.posDef_int_lower {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) :
    ∃ m0 : ℝ, 0 < m0 ∧ ∀ x : Fin N → ℤ, x ≠ 0 →
      m0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ (A *ᵥ fun i => (x i : ℝ)) := by sorry
