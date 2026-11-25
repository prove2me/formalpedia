-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56
-- name    : P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:00.549268+00:00
-- url     : https://prove2.me/theorems/0a10a51d-4198-4568-8223-72d0cba18130
-- title:
--   P2 M Global Theory T symplectic eq parabolic J parabolic J parabolic  6343b5708f56: P2 M Global Theory T symplectic eq parabolic J parabolic J parabolic  6343b5708f56
-- statement:
--   The P2 M Global Theory T symplectic eq parabolic J parabolic J parabolic  6343b5708f56 construction uses the P2 M Global Theory T symplectic eq parabolic J parabolic J parabolic  6343b5708f56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticEqParabolicJParabolicJParabolicStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SymplecticEqParabolicJParabolicJParabolicStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticEqParabolicJParabolicJParabolicStatement
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

theorem P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56 : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∃ p₁ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₂ ∈ Matrix.symplecticGroup ι ℚ, ∃ p₃ ∈ Matrix.symplecticGroup ι ℚ, p₁.toBlocks₂₁ = 0 ∧ p₂.toBlocks₂₁ = 0 ∧ p₃.toBlocks₂₁ = 0 ∧ σ = p₁ * Matrix.J ι ℚ * p₂ * Matrix.J ι ℚ * p₃ := by sorry

alias «GlobalTheory».«T».«symplectic_eq_parabolic_J_parabolic_J_parabolic'» := P2M_GlobalTheory_T_symplectic_eq_parabolic_J_parabolic_J_parabolic__6343b5708f56
