-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_nM_cond_iff
-- name    : PositivityTheory.SiegelWeilFormula.KAway.nM_cond_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:56:42.18003+00:00
-- url     : https://prove2.me/theorems/b32b0367-da70-5bf0-aee5-6ceb27872a6d
-- title:
--   KAway: n M cond iff
-- statement:
--   The KAway construction uses the n M cond iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L18-L21

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

theorem PositivityTheory.SiegelWeilFormula.KAway.nM_cond_iff (t : Matrix (Fin n) (Fin n) R) :
    (nM t)ᵀ * jF n ε * (nM t).map c = jF n ε ↔ tᵀ + (ε : R) • t.map c = 0 := by sorry
