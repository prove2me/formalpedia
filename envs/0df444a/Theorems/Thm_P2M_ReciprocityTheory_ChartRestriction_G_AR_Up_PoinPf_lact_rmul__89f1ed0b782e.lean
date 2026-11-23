-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lact_rmul__89f1ed0b782e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lact_rmul__89f1ed0b782e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:47.167215+00:00
-- url     : https://prove2.me/theorems/0df60dac-1ac4-429d-b523-0cc0782f4b62
-- title:
--   P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf lact rmul  89f1ed0b782e: P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf lact rmul  89f1ed0b782e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf lact rmul  89f1ed0b782e construction uses the P2 M Reciprocity Theory Chart Restriction G AR Up Poin Pf lact rmul  89f1ed0b782e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfA.lean#L34-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PairUnfoldPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.SmoothSeries
import Definitions.Def_Lemmata_GeneralBFactVersion_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lact_rmul__89f1ed0b782e {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«AR».«Up».«PoinPf».«lact_rmul'» := P2M_ReciprocityTheory_ChartRestriction_G_AR_Up_PoinPf_lact_rmul__89f1ed0b782e
