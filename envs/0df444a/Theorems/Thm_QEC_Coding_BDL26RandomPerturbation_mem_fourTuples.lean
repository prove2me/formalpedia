-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mem_fourTuples
-- name    : QEC.Coding.BDL26RandomPerturbation.mem_fourTuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:13:56.500977+00:00
-- url     : https://prove2.me/theorems/6de0d0f2-4185-4bfa-b091-282b45948a07
-- title:
--   BDL26 Random Perturbation: mem four Tuples
-- statement:
--   The BDL26 Random Perturbation construction uses the mem four Tuples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L34-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L34-L38

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.mem_fourTuples {A : Type*} (L : List A) (a b c d : A) :
    [a,b,c,d] ∈ fourTuples L ↔ a ∈ L ∧ b ∈ L ∧ c ∈ L ∧ d ∈ L := by sorry
