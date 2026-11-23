-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_cpt_inj
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.KU.cpt_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:58.520697+00:00
-- url     : https://prove2.me/theorems/de08a89e-e50d-4856-b104-9bee9ddde052
-- title:
--   KU: cpt inj
-- statement:
--   The KU construction uses the cpt inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfB.lean#L217-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfB.lean#L217-L240

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Lemmata_GeneralBFactVariant_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_KaUnfoldPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.KU
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Matrix
open scoped ENNReal ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.KU.cpt_inj (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {z z' : V (nd X)} {b b' : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) (hb' : b' ∈ Bor X.Ψ r) (h : rmul (cpt X x0 z) b = rmul (cpt X x0 z') b') :
    z = z' ∧ b = b' := by sorry
