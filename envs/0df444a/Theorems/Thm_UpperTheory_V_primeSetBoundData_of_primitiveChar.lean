-- Prove2me | Theorems.Thm_UpperTheory_V_primeSetBoundData_of_primitiveChar
-- name    : UpperTheory.V.primeSetBoundData_of_primitiveChar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:54.666911+00:00
-- url     : https://prove2.me/theorems/51483ded-13df-4b52-a063-24f9c7223b42
-- title:
--   V: prime Set Bound Data of primitive Char
-- statement:
--   The V construction uses the prime Set Bound Data of primitive Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L136-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/PrimeSetBoundDataOfPrimitiveChar.lean#L136-L137

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_StmtFields
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PrimeSetBoundDataOfPrimitiveChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open UpperTheory UpperTheory.V
open Formalism.HC UpperTheory.Top

theorem UpperTheory.V.primeSetBoundData_of_primitiveChar (ψ : PChar) : OddPrimesWithRootsOfUnity (Bchi ψ) (Lchi ψ) := by sorry
