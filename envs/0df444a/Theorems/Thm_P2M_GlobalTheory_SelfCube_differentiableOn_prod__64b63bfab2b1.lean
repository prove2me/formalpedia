-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
-- name    : P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:53.607798+00:00
-- url     : https://prove2.me/theorems/e1f4542e-04d8-4bba-84f0-32a598b15c44
-- title:
--   P2 M Global Theory Self Cube differentiable On prod  64b63bfab2b1: P2 M Global Theory Self Cube differentiable On prod  64b63bfab2b1
-- statement:
--   The P2 M Global Theory Self Cube differentiable On prod  64b63bfab2b1 construction uses the P2 M Global Theory Self Cube differentiable On prod  64b63bfab2b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L216-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L216-L222

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube

theorem P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1 {g : ℕ} {α : Type*} {f : α → (Fin g → ℂ) → ℂ} {S : Set (Fin g → ℂ)}
    (s : Finset α) (hf : ∀ i, DifferentiableOn ℂ (f i) S) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) S := by sorry

alias «GlobalTheory».«SelfCube».«differentiableOn_prod'» := P2M_GlobalTheory_SelfCube_differentiableOn_prod__64b63bfab2b1
