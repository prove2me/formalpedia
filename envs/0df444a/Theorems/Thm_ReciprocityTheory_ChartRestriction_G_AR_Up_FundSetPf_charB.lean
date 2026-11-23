-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_FundSetPf_charB
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.charB
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:54:13.762494+00:00
-- url     : https://prove2.me/theorems/4f860329-7c34-4696-80b0-d301440253bd
-- title:
--   Fund Set Pf: char B
-- statement:
--   The Fund Set Pf construction uses the char B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L61-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/FundSetPf.lean#L61-L86

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfD
import Definitions.Def_Lemmata_GeneralBFactTer_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Set
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.charB {Ψ : Finset (E →+* ℂ)} (δ : GL (Fin r) E) {y y' : Frame Ψ r}
    (hy : ∀ τ, (mat y τ).det ≠ 0) (hy' : ∀ τ, (mat y' τ).det ≠ 0) :
    (∃ b ∈ Bor Ψ r, lact δ y = rmul y' b) ↔ ∀ τ : Ψ, ∀ a c : Fin r, c < a →
      ((mat y' τ).adjugate * (δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ) a c = 0 := by sorry
