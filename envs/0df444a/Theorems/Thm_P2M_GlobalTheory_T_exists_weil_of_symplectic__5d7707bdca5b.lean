-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_weil_of_symplectic__5d7707bdca5b
-- name    : P2M_GlobalTheory_T_exists_weil_of_symplectic__5d7707bdca5b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:13:05.412405+00:00
-- url     : https://prove2.me/theorems/ed9339d3-183a-4d64-87a2-ff6047cff40f
-- title:
--   P2 M Global Theory T exists weil of symplectic  5d7707bdca5b: P2 M Global Theory T exists weil of symplectic  5d7707bdca5b
-- statement:
--   The P2 M Global Theory T exists weil of symplectic  5d7707bdca5b construction uses the P2 M Global Theory T exists weil of symplectic  5d7707bdca5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsWeilOfSymplecticStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsWeilOfSymplecticStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplectic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsWeilOfSymplecticStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_weil_of_symplectic__5d7707bdca5b : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), Even (Fintype.card κ) → σ ∈ Matrix.symplecticGroup ι ℚ → ∃ ω : (Matrix κ ι ℚ → ℂ) → (Matrix κ ι ℚ → ℂ), ∀ φ, IsSB φ → IsSB (ω φ) ∧ TransS σ φ (ω φ) ∧ ∀ φ', IsSB φ' → ip (ω φ) (ω φ') = ip φ φ' := by sorry

alias «GlobalTheory».«T».«exists_weil_of_symplectic'» := P2M_GlobalTheory_T_exists_weil_of_symplectic__5d7707bdca5b
