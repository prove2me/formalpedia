-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_class_normal_form
-- name    : QEC.Coding.BDL26FiniteCohomology.class_normal_form
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:29:45.511229+00:00
-- url     : https://prove2.me/theorems/282ac920-7b6c-42bf-ae61-52be982610f9
-- title:
--   BDL26 Finite Cohomology: class normal form
-- statement:
--   Every actual global cocycle class has its computed scalar normal form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L168-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L168-L173

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

theorem QEC.Coding.BDL26FiniteCohomology.class_normal_form (S : OddScale) (n : Nat) (v : Cocycle S n) :
    classOf S n v = classOf S n (generator S n (finiteH1Equiv S n (classOf S n v))) := by sorry
