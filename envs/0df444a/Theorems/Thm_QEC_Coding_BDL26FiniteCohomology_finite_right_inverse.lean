-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finite_right_inverse
-- name    : QEC.Coding.BDL26FiniteCohomology.finite_right_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:28:58.813106+00:00
-- url     : https://prove2.me/theorems/c92e06f2-f238-44e8-934c-fb01bd027325
-- title:
--   BDL26 Finite Cohomology: finite right inverse
-- statement:
--   The BDL26 Finite Cohomology construction uses the finite right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L138-L139
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L138-L139

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.finite_right_inverse (S : OddScale) (n : Nat) (c : Field) :
    finiteH1Equiv S n ((finiteH1Equiv S n).symm c) = c := by sorry
