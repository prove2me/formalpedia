-- Prove2me | Theorems.Thm_P2M_GlobalTheory_SatMinor_exists_minor_ne_zero__d04f3c26b9e3
-- name    : P2M_GlobalTheory_SatMinor_exists_minor_ne_zero__d04f3c26b9e3
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:08:50.009098+00:00
-- url     : https://prove2.me/theorems/ffc3a253-8a2d-4dab-a685-32c0a2f8e3e3
-- title:
--   P2 M Global Theory Sat Minor exists minor ne zero  d04f3c26b9e3: P2 M Global Theory Sat Minor exists minor ne zero  d04f3c26b9e3
-- statement:
--   The P2 M Global Theory Sat Minor exists minor ne zero  d04f3c26b9e3 construction uses the P2 M Global Theory Sat Minor exists minor ne zero  d04f3c26b9e3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitMinorOfIntegralMatrix.lean#L34-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitMinorOfIntegralMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SatMinor
variable {p : ℕ} [Fact p.Prime]

theorem P2M_GlobalTheory_SatMinor_exists_minor_ne_zero__d04f3c26b9e3 {K : Type} [Field K] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J]
    (M : Matrix κ J K) (hM : LinearIndependent K M.row) :
    ∃ f : κ → J, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by sorry

alias «GlobalTheory».«SatMinor».«exists_minor_ne_zero'» := P2M_GlobalTheory_SatMinor_exists_minor_ne_zero__d04f3c26b9e3
