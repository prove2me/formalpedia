-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_generator_value
-- name    : QEC.Coding.BDL26FiniteCohomology.generator_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:26:01.350202+00:00
-- url     : https://prove2.me/theorems/1cf81bd0-298a-4c92-9393-2042fecfe8aa
-- title:
--   BDL26 Finite Cohomology: generator value
-- statement:
--   The BDL26 Finite Cohomology construction uses the generator value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L163-L165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L163-L165

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.generator_value (S : OddScale) (n : Nat) (c : Field) :
    (generator S n c).1 = BDL26AlternatingCochain.map1 S n
      (c • BDL26SeedCohomology.seedElement).1 := by sorry

attribute [defeq] QEC.Coding.BDL26FiniteCohomology.generator_value
