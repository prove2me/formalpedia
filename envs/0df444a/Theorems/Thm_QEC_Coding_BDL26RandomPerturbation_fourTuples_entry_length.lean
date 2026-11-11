-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuples_entry_length
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuples_entry_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:56:29.086079+00:00
-- url     : https://prove2.me/theorems/9fb3f2c8-b6b8-4521-9aa0-ca74c759fdb2
-- title:
--   BDL26 Random Perturbation: four Tuples entry length
-- statement:
--   All four-loop candidates have exactly four list entries, before duplicate filtering.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L53-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L53-L57

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fourTuples_entry_length {A : Type*} (L : List A) (t : List A)
    (h : t ∈ fourTuples L) : t.length = 4 := by sorry
