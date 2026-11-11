-- Prove2me | Theorems.Thm_QEC_Coding_BDL26GlobalLookupLinearity_lookup_eq_global_of_local_none
-- name    : QEC.Coding.BDL26GlobalLookupLinearity.lookup_eq_global_of_local_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:26:38.835971+00:00
-- url     : https://prove2.me/theorems/bf6b165d-d6d4-451f-81ec-0e539cec0a51
-- title:
--   BDL26 Global Lookup Linearity: lookup eq global of local none
-- statement:
--   Exact failed-local branch of the unchanged generic lookup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L286-L292
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/GlobalLookupLinearity.lean#L286-L292

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LevelTwoDecoderZero
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GlobalLookupLinearity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26GlobalLookupLinearity
open BDL26LevelTwoDecoder BDL26FiniteTannerSquare BDL26LevelTwoCode
open BDL26RZMap1CoordinateBridge
open scoped BigOperators
variable {A B : Type} [Fintype A] [Encodable A] [DecidableEq A]
variable [Fintype B] [DecidableEq B]

theorem QEC.Coding.BDL26GlobalLookupLinearity.lookup_eq_global_of_local_none (L : Word Bit A →ₗ[Bit] Word Bit B)
    (isLocal : Word Bit A → Bool) (s : Word Bit B)
    (h : search (fun e => isLocal e && decide (L e=s)) (allWords A)=none) :
    lookup (allWords A) L isLocal 0 s=G L s := by sorry
