-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lminor_gM_rmul
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.lminor_gM_rmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:45:52.604187+00:00
-- url     : https://prove2.me/theorems/d64daa67-30e5-4f2a-9075-7fda6460eb17
-- title:
--   Poin Pf: lminor g M rmul
-- statement:
--   The Poin Pf construction uses the lminor g M rmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfF.lean#L251-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfF.lean#L251-L256

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.lminor_gM_rmul (X : Data E r) (x0 y : Frame X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (τ : X.Ψ) (i : Fin (r + 1)) :
    lminor (gM X x0 (rmul y b) τ) i = lminor (gM X x0 y τ) i * ∏ j : Fin i,
      mat b τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by sorry
