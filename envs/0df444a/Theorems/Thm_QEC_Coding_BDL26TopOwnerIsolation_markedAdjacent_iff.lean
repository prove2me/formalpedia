-- Prove2me | Theorems.Thm_QEC_Coding_BDL26TopOwnerIsolation_markedAdjacent_iff
-- name    : QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T00:12:10.801029+00:00
-- url     : https://prove2.me/theorems/4816dc74-90dc-4783-84c5-c60635adf27a
-- title:
--   BDL26 Top Owner Isolation: marked Adjacent iff
-- statement:
--   The BDL26 Top Owner Isolation construction uses the marked Adjacent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L34-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/TopOwnerIsolation.lean#L34-L36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_DecodingGraph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TopOwnerIsolation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26TopOwnerIsolation
open BDL26FiniteTannerSquare BDL26DecodingGraph MultiscaleDecoder
open scoped Classical

theorem QEC.Coding.BDL26TopOwnerIsolation.markedAdjacent_iff (M : Finset Node)
    (u v : {w : Node // w ∈ M}) :
    markedAdjacent M u v ↔ graph.adjacent u.val v.val := by sorry
