-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_columnHits_iff_not_columnAvoids
-- name    : QEC.Coding.FiberBundle.RandomBase.columnHits_iff_not_columnAvoids
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:51:47.278224+00:00
-- url     : https://prove2.me/theorems/a5cc52b0-315a-4c4d-b99b-52adee43b941
-- title:
--   Random Base: column Hits iff not column Avoids
-- statement:
--   Being hit is exactly the complement of avoiding all selected checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L43-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/RandomBase/ExpansionProbability.lean#L43-L64

import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Expansion
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomBase.columnHits_iff_not_columnAvoids
    {r : Nat} (S : Finset (Fin (3 * r)))
    (column : ColumnSample r) :
    ColumnHits S column ↔ ¬ColumnAvoids S column := by sorry
