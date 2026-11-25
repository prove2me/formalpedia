-- Prove2me | Theorems.Thm_UpperTheory_V_isCompField_ofChar
-- name    : UpperTheory.V.isCompField_ofChar
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:49:37.105495+00:00
-- url     : https://prove2.me/theorems/d25cf029-bdef-4741-91a9-0a47976968cb
-- title:
--   V: is Comp Field of Char
-- statement:
--   The V construction uses the is Comp Field of Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/StmtFields.lean#L91-L94

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

theorem UpperTheory.V.isCompField_ofChar (ψ : PChar) (e q d : ℕ) (E : Type) [Field E] [NumberField E] :
    IsCompField (AbF.ofChar ψ) e q d E ↔ IsChiField ψ e q d E := by sorry
