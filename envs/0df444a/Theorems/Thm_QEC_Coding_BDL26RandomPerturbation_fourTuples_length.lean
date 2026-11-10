-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_fourTuples_length
-- name    : QEC.Coding.BDL26RandomPerturbation.fourTuples_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:12:02.997509+00:00
-- url     : https://prove2.me/theorems/8bc5aaf1-a74d-4da4-ad5b-cfd8b5d7f64a
-- title:
--   BDL26 Random Perturbation: four Tuples length
-- statement:
--   The BDL26 Random Perturbation construction uses the four Tuples length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L26-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L26-L32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.fourTuples_length {A : Type*} (L : List A) : (fourTuples L).length = L.length^4 := by sorry
