-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BK_Descent_Hom_app_mem_Y__a74defe19476
-- name    : P2M_GlobalTheory_BK_Descent_Hom_app_mem_Y__a74defe19476
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:07:29.007368+00:00
-- url     : https://prove2.me/theorems/86976459-bef5-45dc-a4c7-611196abfb47
-- title:
--   P2 M Global Theory BK Descent Hom app mem Y  a74defe19476: P2 M Global Theory BK Descent Hom app mem Y  a74defe19476
-- statement:
--   The P2 M Global Theory BK Descent Hom app mem Y  a74defe19476 construction uses the P2 M Global Theory BK Descent Hom app mem Y  a74defe19476 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L210-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_ExistsEqAlgebraMapAddPowMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TameDescentExtendedActionExtraVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.BK
open PowerSeries Filter Topology Matrix
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]
  [TameDescentExponentData K l e a]
open GlobalTheory.BK.Descent
variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {T : PhiMod O K l e a μ}
open GlobalTheory.BK.Descent.Hom
variable {Δ₁ : Descent P} {Δ₂ : Descent Q} {Δ₃ : Descent T} (F : Hom Δ₁ Δ₂)
omit [NeZero e]

theorem P2M_GlobalTheory_BK_Descent_Hom_app_mem_Y__a74defe19476 {η : ℕ} {y : Vec K a ι} (hy : y ∈ Δ₁.Y' η) : F.app y ∈ Δ₂.Y' η := by sorry

alias «GlobalTheory».«BK».«Descent».«Hom».«app_mem_Y'» := P2M_GlobalTheory_BK_Descent_Hom_app_mem_Y__a74defe19476
