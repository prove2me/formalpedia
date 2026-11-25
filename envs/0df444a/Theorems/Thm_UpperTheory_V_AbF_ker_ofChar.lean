-- Prove2me | Theorems.Thm_UpperTheory_V_AbF_ker_ofChar
-- name    : UpperTheory.V.AbF.ker_ofChar
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:13:47.652716+00:00
-- url     : https://prove2.me/theorems/1c018f9a-90d7-5911-9ce9-43c51b58181c
-- title:
--   Ab F: ker of Char
-- statement:
--   The Ab F construction uses the ker of Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L73-L89

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Polynomial
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top

theorem UpperTheory.V.AbF.ker_ofChar (ψ : PChar) (a : ℕ) : (AbF.ofChar ψ).ker a ↔ ψ.val a = 1 := by sorry
