-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_sumBdIsUpq_right
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:00:01.869011+00:00
-- url     : https://prove2.me/theorems/06e9954a-40c7-53e5-8dcd-7c65a0676614
-- title:
--   Up: sum Bd Is Upq right
-- statement:
--   The Up construction uses the sum Bd Is Upq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatementPfA.lean#L15-L22

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdIsUpq_right {M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (h : IsUpq M) :
    M * Jf p q * Mᴴ = Jf p q := by sorry
