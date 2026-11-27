-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_upper_block_rank_one_update
-- name    : PositivityTheory.SiegelWeilFormula.KAway.upper_block_rank_one_update
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:46.481934+00:00
-- url     : https://prove2.me/theorems/3a5bdfa3-dbc3-5857-8115-d01df5dba9b0
-- title:
--   KAway: upper block rank one update
-- statement:
--   The KAway construction uses the upper block rank one update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L23-L31

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_AwayActions_DecAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open Matrix
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KAway
variable {R : Type} [CommRing R] {n : ℕ}
variable (c : R →+* R) (ε : ℤ)

theorem PositivityTheory.SiegelWeilFormula.KAway.upper_block_rank_one_update (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hM : Mᵀ * jF n ε * M.map c = jF n ε) :
    (M.toBlocks₁₁)ᵀ * (M.toBlocks₂₁).map c + (ε : R) • ((M.toBlocks₂₁)ᵀ * (M.toBlocks₁₁).map c) = 0 := by sorry
