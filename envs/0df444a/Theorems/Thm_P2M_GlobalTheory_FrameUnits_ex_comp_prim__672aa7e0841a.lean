-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FrameUnits_ex_comp_prim__672aa7e0841a
-- name    : P2M_GlobalTheory_FrameUnits_ex_comp_prim__672aa7e0841a
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:06:30.128715+00:00
-- url     : https://prove2.me/theorems/d9dc48f0-cf6c-5125-8b2e-b18947b993bf
-- title:
--   P2 M Global Theory Frame Units ex comp prim  672aa7e0841a: P2 M Global Theory Frame Units ex comp prim  672aa7e0841a
-- statement:
--   The P2 M Global Theory Frame Units ex comp prim  672aa7e0841a construction uses the P2 M Global Theory Frame Units ex comp prim  672aa7e0841a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L272-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/TripleProductTorusPeriodicBounded.lean#L272-L284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TripleProductTorusPeriodicBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open GlobalTheory.JetSer (IsNormRos primφ primε)
open GlobalTheory.CubeValues GlobalTheory.AppellHumbertTrivial
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.FrameUnits
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem P2M_GlobalTheory_FrameUnits_ex_comp_prim__672aa7e0841a {w : A ⟶ A} {W : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)} (hW : ∀ z, u.ex (W z) = u.ex z ≫ w)
    (k : Fin 5) (z : Fin g → ℂ) : (u.ex z).left ≫ primφ w k = (u.ex (primLin W k z)).left := by sorry

alias «GlobalTheory».«FrameUnits».«ex_comp_primφ» := P2M_GlobalTheory_FrameUnits_ex_comp_prim__672aa7e0841a
