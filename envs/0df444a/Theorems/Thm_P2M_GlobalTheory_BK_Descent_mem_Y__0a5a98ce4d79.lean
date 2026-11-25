-- Prove2me | Theorems.Thm_P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79
-- name    : P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:03:17.711795+00:00
-- url     : https://prove2.me/theorems/5a752fa8-8dbe-409f-8c2e-1aa293bdeb6c
-- title:
--   P2 M Global Theory BK Descent mem Y  0a5a98ce4d79: P2 M Global Theory BK Descent mem Y  0a5a98ce4d79
-- statement:
--   The P2 M Global Theory BK Descent mem Y  0a5a98ce4d79 construction uses the P2 M Global Theory BK Descent mem Y  0a5a98ce4d79 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TameDescentExtendedActionExtraVector.lean#L66-L67

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
variable {P : PhiMod O K l e a ι} (Δ : Descent P)
omit [NeZero e]

theorem P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79 {η : ℕ} {y : Vec K a ι} : y ∈ Δ.Y' η ↔ ∃ y₀ ∈ Δ.Y η, (X : K⟦X⟧) ^ e • y₀ = y := by sorry

alias «GlobalTheory».«BK».«Descent».«mem_Y'» := P2M_GlobalTheory_BK_Descent_mem_Y__0a5a98ce4d79
