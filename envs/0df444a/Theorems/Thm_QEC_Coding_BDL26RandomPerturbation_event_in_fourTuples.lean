-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_event_in_fourTuples
-- name    : QEC.Coding.BDL26RandomPerturbation.event_in_fourTuples
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T22:04:36.521276+00:00
-- url     : https://prove2.me/theorems/750725c7-b020-4844-858c-2dd91abca5a0
-- title:
--   BDL26 Random Perturbation: event in four Tuples
-- statement:
--   Every eligible event is found by these four loops over the actual input labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L41-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/FourTupleEnumeration.lean#L41-L50

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventEncoding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FourTupleEnumeration
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RandomPerturbation.event_in_fourTuples (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius : ℝ) (e : Event P J radius) :
    ∃ L ∈ fourTuples (Finset.univ.toList : List (Triangle P)), L.toFinset = e.val := by sorry
