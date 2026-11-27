-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_blkUpper
-- name    : PositivityTheory.SiegelWeilFormula.KAway.blkUpper
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:50.085677+00:00
-- url     : https://prove2.me/theorems/64e058e3-097e-4459-966d-48318770ec78
-- title:
--   KAway: blk Upper
-- statement:
--   The KAway construction uses the blk Upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L33-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L33-L39

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

theorem PositivityTheory.SiegelWeilFormula.KAway.blkUpper (A B D : Matrix (Fin n) (Fin n) R) (hM : (fromBlocks A B 0 D)ᵀ * jF n ε * (fromBlocks A B 0 D).map c = jF n ε) :
    Aᵀ * D.map c = 1 ∧ Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0 := by sorry
