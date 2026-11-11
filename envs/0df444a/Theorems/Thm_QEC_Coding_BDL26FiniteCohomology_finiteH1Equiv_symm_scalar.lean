-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_finiteH1Equiv_symm_scalar
-- name    : QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_symm_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:27:24.321915+00:00
-- url     : https://prove2.me/theorems/16e7fad7-a0c1-4e04-9509-d6f86c56d798
-- title:
--   BDL26 Finite Cohomology: finite H1 Equiv symm scalar
-- statement:
--   The inverse on every scalar is the literal selected prefix seed generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L152-L157
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L152-L157

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

theorem QEC.Coding.BDL26FiniteCohomology.finiteH1Equiv_symm_scalar (S : OddScale) (n : Nat) (c : Field) :
    (finiteH1Equiv S n).symm c = classOf S n
      (prefixCocycle S n (c • BDL26SeedCohomology.seedElement)) := by sorry
