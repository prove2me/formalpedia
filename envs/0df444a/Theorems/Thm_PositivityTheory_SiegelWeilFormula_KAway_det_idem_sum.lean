-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_KAway_det_idem_sum
-- name    : PositivityTheory.SiegelWeilFormula.KAway.det_idem_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:57:12.504509+00:00
-- url     : https://prove2.me/theorems/85438a6f-1c58-4017-a8f4-c9e615bd3f4b
-- title:
--   KAway: det idem sum
-- statement:
--   The KAway construction uses the det idem sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L41-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/AwayActions/DecAlg.lean#L41-L61

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

theorem PositivityTheory.SiegelWeilFormula.KAway.det_idem_sum {ι : Type} [Fintype ι] (f : ι → R) (hf : ∀ i, f i * f i = f i) (ho : ∀ i j, i ≠ j → f i * f j = 0)
    (h1 : ∑ i, f i = 1) (M : ι → Matrix (Fin n) (Fin n) R) : (∑ i, f i • M i).det = ∑ i, f i * (M i).det := by sorry
