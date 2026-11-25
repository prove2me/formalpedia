-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_normal_finiteType_subring_le_valuationSubring__20ddf3e6c463
-- name    : P2M_GlobalTheory_T_exists_normal_finiteType_subring_le_valuationSubring__20ddf3e6c463
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:30:58.234441+00:00
-- url     : https://prove2.me/theorems/49c9885d-99c0-5064-a407-511167e2d0d4
-- title:
--   P2 M Global Theory T exists normal finite Type subring le valuation Subring  20ddf3e6c463: P2 M Global Theory T exists normal finite Type subring le valuation Subring  20ddf3e6c463
-- statement:
--   The P2 M Global Theory T exists normal finite Type subring le valuation Subring  20ddf3e6c463 construction uses the P2 M Global Theory T exists normal finite Type subring le valuation Subring  20ddf3e6c463 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormalFiniteTypeSubringLeValuationSubringAStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNormalFiniteTypeSubringLeValuationSubringAStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringLeValuationSubringA
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNormalFiniteTypeSubringLeValuationSubringAStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_normal_finiteType_subring_le_valuationSubring__20ddf3e6c463 : ∀ {κ : Type} [Field κ] [Algebra ℂ κ] (V : ValuationSubring κ) (T : Finset κ), (∀ a : ℂ, algebraMap ℂ κ a ∈ V) → (∀ x ∈ T, x ∈ V) → (∀ f : κ, ∃ a ∈ Algebra.adjoin ℂ (T : Set κ), ∃ b ∈ Algebra.adjoin ℂ (T : Set κ), b ≠ 0 ∧ f * b = a) → ∃ (R : Subring κ) (hcR : ∀ a : ℂ, algebraMap ℂ κ a ∈ R), ((algebraMap ℂ κ).codRestrict R hcR).FiniteType ∧ (∀ x ∈ T, x ∈ R) ∧ R ≤ V.toSubring ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧ IsFractionRing R κ := by sorry

alias «GlobalTheory».«T».«exists_normal_finiteType_subring_le_valuationSubring'» := P2M_GlobalTheory_T_exists_normal_finiteType_subring_le_valuationSubring__20ddf3e6c463
