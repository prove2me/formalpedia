-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_flatMap_length_of_const
-- name    : QEC.Coding.BDL26RandomPerturbation.flatMap_length_of_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T03:04:02.656045+00:00
-- url     : https://prove2.me/theorems/a90e4415-d873-4677-be3a-435d077d3a44
-- title:
--   BDL26 Random Perturbation: flat Map length of const
-- statement:
--   The BDL26 Random Perturbation construction uses the flat Map length of const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L17-L24
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L17-L24

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.flatMap_length_of_const {A B : Type*} (L : List A) (f : A → List B) (C : ℕ)
    (h : ∀ a ∈ L, (f a).length = C) : (L.flatMap f).length = L.length*C := by sorry
