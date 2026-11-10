-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefixEquiv_succ
-- name    : QEC.Coding.BDL26FiniteCohomology.prefixEquiv_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:28:16.850871+00:00
-- url     : https://prove2.me/theorems/b1cc6d17-cd5b-4916-a418-2a1983dbc014
-- title:
--   BDL26 Finite Cohomology: prefix Equiv succ
-- statement:
--   The BDL26 Finite Cohomology construction uses the prefix Equiv succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L81-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L81-L82

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_SeedCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RZCohomology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_FiniteCohomology
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26FiniteCohomology
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26AlternatingCochain
open BDL26ReplacementCochainMaps BDL26RZMap1CoordinateBridge
open BDL26IndexedDecoder MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26FiniteCohomology.prefixEquiv_succ (S : OddScale) (n : Nat) :
    prefixEquiv S (n+1) = (prefixEquiv S n).trans (stepEquiv S n) := by sorry
