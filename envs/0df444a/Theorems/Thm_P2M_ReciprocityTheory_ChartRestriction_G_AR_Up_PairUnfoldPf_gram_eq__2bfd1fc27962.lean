-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_gram_eq__2bfd1fc27962
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_gram_eq__2bfd1fc27962
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:45.221265+00:00
-- url     : https://prove2.me/theorems/06de5a20-b9fc-4bb0-b9c4-dfbb437d7e66
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Pair Unfold Pf gram eq  2bfd1fc27962: P2 M Reciprocity Theory Chart Restriction G AR Up Pair Unfold Pf gram eq  2bfd1fc27962
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Pair Unfold Pf gram eq  2bfd1fc27962 construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Pair Unfold Pf gram eq  2bfd1fc27962 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfA.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PairUnfoldPfA.lean#L31-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_gram_eq__2bfd1fc27962 (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = M.transpose * G.map τ * M.map (starRingEnd ℂ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PairUnfoldPf».«gram_eq'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PairUnfoldPf_gram_eq__2bfd1fc27962
