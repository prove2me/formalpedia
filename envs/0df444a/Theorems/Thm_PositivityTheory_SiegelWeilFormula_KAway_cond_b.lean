-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_cond_b
-- name    : PositivityTheory.SiegelWeilFormula.KAway.cond_b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:38.3918+00:00
-- url     : https://prove2.me/theorems/1d8d6d0f-3533-5c48-9f1a-fc569cc61bec
-- title:
--   KAway: cond b
-- statement:
--   The KAway construction uses the cond b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L139-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L139-L155

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

theorem PositivityTheory.SiegelWeilFormula.KAway.cond_b (hc : ∀ z, c (c z) = z) (A B D : Matrix (Fin n) (Fin n) R) (hA : IsUnit A.det) (h1 : Aᵀ * D.map c = 1)
    (h2 : Bᵀ * D.map c + (ε : R) • (Dᵀ * B.map c) = 0) : (A⁻¹ * B)ᵀ + (ε : R) • (A⁻¹ * B).map c = 0 := by sorry
