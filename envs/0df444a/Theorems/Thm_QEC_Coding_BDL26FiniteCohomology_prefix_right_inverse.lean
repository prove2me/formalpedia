-- Prove2me | Theorems.Thm_QEC_Coding_BDL26FiniteCohomology_prefix_right_inverse
-- name    : QEC.Coding.BDL26FiniteCohomology.prefix_right_inverse
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:48:43.156031+00:00
-- url     : https://prove2.me/theorems/fca98935-797a-49ac-86a3-cd68b955cc3a
-- title:
--   BDL26 Finite Cohomology: prefix right inverse
-- statement:
--   The BDL26 Finite Cohomology construction uses the prefix right inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L123-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/FiniteCohomology.lean#L123-L124

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

theorem QEC.Coding.BDL26FiniteCohomology.prefix_right_inverse (S : OddScale) (n : Nat) (v : H1 S n) :
    prefixEquiv S n ((prefixEquiv S n).symm v) = v := by sorry
