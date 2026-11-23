-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_KU_rho_apply
-- name    : ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rho_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:12:49.917717+00:00
-- url     : https://prove2.me/theorems/a2e7b93c-42de-460c-91ec-7e58b93f0206
-- title:
--   KU: rho apply
-- statement:
--   The KU construction uses the rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfB.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/KaUnfoldPfB.lean#L62-L65

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

theorem ReciprocityTheory.ChartRestriction.G.AR.Up.KU.rho_apply (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (γ : GL (Fin r) E)
    (k : Fin (Fintype.card X.Ψ)) :
    ((rho X ho γ k : GL (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) : Matrix _ _ ℂ) =
      gm X x0 γ ((Fintype.equivFin X.Ψ).symm k) := by sorry
