-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_mass_not_rootsAvoid_le__80e9465e9883
-- name    : P2M_GlobalTheory_T_mass_not_rootsAvoid_le__80e9465e9883
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:59:54.424339+00:00
-- url     : https://prove2.me/theorems/b6aa7ea0-5cf6-47f2-ba04-b98027adaf6c
-- title:
--   P2 M Global Theory T mass not roots Avoid le  80e9465e9883: P2 M Global Theory T mass not roots Avoid le  80e9465e9883
-- statement:
--   The P2 M Global Theory T mass not roots Avoid le  80e9465e9883 construction uses the P2 M Global Theory T mass not roots Avoid le  80e9465e9883 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MassNotRootsAvoidLeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/MassNotRootsAvoidLeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassNotRootsAvoidLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_mass_not_rootsAvoid_le__80e9465e9883 : ∀ (g : ℕ) [Fact g.Prime], ∀ (N q d : ℕ) (c : (ZMod g)ˣ), (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → (mass g N fun f => ¬ RootsAvoid g c f) ≤ 1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1) := by sorry

alias «GlobalTheory».«T».«mass_not_rootsAvoid_le'» := P2M_GlobalTheory_T_mass_not_rootsAvoid_le__80e9465e9883
