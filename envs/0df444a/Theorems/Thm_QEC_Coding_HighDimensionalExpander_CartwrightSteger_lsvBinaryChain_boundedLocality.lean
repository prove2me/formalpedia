-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_lsvBinaryChain_boundedLocality
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBinaryChain_boundedLocality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T18:38:25.663846+00:00
-- url     : https://prove2.me/theorems/60f5c1eb-e677-421f-bf24-3eb977304e97
-- title:
--   Cartwright Steger: lsv Binary Chain bounded Locality
-- statement:
--   The binary chain complex has a locality bound independent of the quotient
--   level.  Only `P`, `r`, and the selected chain degree occur in the bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1627-L1638
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/QuotientComplex.lean#L1627-L1638

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvBinaryChain_boundedLocality
    (P : BasePrime) (r : Rank) (level p : Nat) (hp : 1 ≤ p) :
    QEC.Coding.BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence
        (lsvBinaryChainAt P r level p)).localityProfile
      (max (max (2 * indexColoredGeneratorBound P r) (p + 2))
        (p + 1 + 2 * indexColoredGeneratorBound P r)) := by sorry
