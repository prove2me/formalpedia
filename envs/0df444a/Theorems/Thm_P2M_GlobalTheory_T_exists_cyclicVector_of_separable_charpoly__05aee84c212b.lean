-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b
-- name    : P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:09:56.571068+00:00
-- url     : https://prove2.me/theorems/ad6a96f0-4c56-4609-853e-908e11bc1143
-- title:
--   P2 M Global Theory T exists cyclic Vector of separable charpoly  05aee84c212b: P2 M Global Theory T exists cyclic Vector of separable charpoly  05aee84c212b
-- statement:
--   The P2 M Global Theory T exists cyclic Vector of separable charpoly  05aee84c212b construction uses the P2 M Global Theory T exists cyclic Vector of separable charpoly  05aee84c212b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCyclicVectorOfSeparableCharpolyStatement.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCyclicVectorOfSeparableCharpolyStatement.lean#L8-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpoly
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCyclicVectorOfSeparableCharpolyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b : ∀ {K : Type} [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable →
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by sorry

alias «GlobalTheory».«T».«exists_cyclicVector_of_separable_charpoly'» := P2M_GlobalTheory_T_exists_cyclicVector_of_separable_charpoly__05aee84c212b
