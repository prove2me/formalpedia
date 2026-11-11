-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_global_normal_form
-- name    : QEC.Coding.BDL26FiniteCohomology.global_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:29:04.601805+00:00
-- url     : https://prove2.me/theorems/faa657bd-c489-4257-8a54-59c6fb4aa566
-- title:
--   BDL26 Finite Cohomology: global normal form
-- statement:
--   Extract a real global degree-zero potential from quotient equality. This
--   is a full-word normal form, including all auxiliary replacement coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L177-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L177-L193

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

theorem QEC.Coding.BDL26FiniteCohomology.global_normal_form (S : OddScale) (n : Nat) (v : Cocycle S n) :
    ∃ f : Word Field (state S n).presentation.X,
      v.1 = tannerCoboundary0 (state S n).presentation f +
        (generator S n (finiteH1Equiv S n (classOf S n v))).1 := by sorry
