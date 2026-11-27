-- Prove2me | Theorems.Thm_UpperTheory_nu_det_mul_sliceB_block_action
-- name    : UpperTheory.nu_det_mul_sliceB_block_action
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:35.5885+00:00
-- url     : https://prove2.me/theorems/858be901-2f73-4d9f-928a-3138e5d7a555
-- title:
--   Upper Theory: nu det mul slice B block action
-- statement:
--   The Upper Theory construction uses the nu det mul slice B block action property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/NuDetMulSliceBBlockAction.lean#L20-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DivisorFrames/NuDetMulSliceBBlockAction.lean#L20-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ScaledIntegerPeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SplitThetaGridPathAvoidsOppositeCorner
import Definitions.Def_Development_AutomorphicArithmetic_DivisorFrames_NuDetMulSliceBBlockAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.nu_det_mul_sliceB_block_action :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k} (ϖ : kˣ) (e : ℕ) (St : G.PiLocalization₂) (i j : ℕ), PassesThrough i j St.path → St.IsAdmissible .one ϖ e → ∀ u ∈ St.level (i, j), ∀ (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k), (G.nu i j (gdet u⁻¹) : ℂ) * G.sliceB i j St.tensor x (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂)) = G.sliceB i j St.tensor x Z := by sorry
