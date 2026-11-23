-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:41:58.827322+00:00
-- url     : https://prove2.me/theorems/dc01f4de-4c39-4566-907f-532734fa1462
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pull U res  1e3fd2a0fd54: P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pull U res  1e3fd2a0fd54
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pull U res  1e3fd2a0fd54 construction uses the P2 M Reciprocity Theory Chart Restriction G Pdiv Pullback Comparison pull U res  1e3fd2a0fd54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L43-L49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54 {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (fun _ hy => h hy : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (pullU f U x) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«Pdiv».«PullbackComparison».«pullU_res'» := P2M_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_pullU_res__1e3fd2a0fd54
