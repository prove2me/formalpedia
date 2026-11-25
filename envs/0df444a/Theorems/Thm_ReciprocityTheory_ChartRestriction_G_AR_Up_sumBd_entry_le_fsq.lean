-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBd_entry_le_fsq
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_entry_le_fsq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:02.954829+00:00
-- url     : https://prove2.me/theorems/661be65b-48bf-5036-b20a-42fa51419ec9
-- title:
--   Up: sum Bd entry le fsq
-- statement:
--   The Up construction uses the sum Bd entry le fsq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L65-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up
open Matrix Topology Filter
open scoped Matrix ComplexOrder ENNReal
noncomputable section
variable {p q : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_entry_le_fsq {m n : Type*} [Fintype m] [Fintype n] (X : Matrix m n ℂ) (i : m) (j : n) :
    Complex.normSq (X i j) ≤ sumBdFsq X := by sorry
