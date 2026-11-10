-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_rxDegreeZero_parent
-- name    : QEC.Coding.BDL26RXDecoderAdapter.rxDegreeZero_parent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:17:12.311232+00:00
-- url     : https://prove2.me/theorems/427c6dfc-0019-48d5-a89a-657e810f8a58
-- title:
--   BDL26 RXDecoder Adapter: rx Degree Zero parent
-- statement:
--   The actual upper X chart computes the existing partial graph parent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1730-L1736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXDecoderAdapter.lean#L1730-L1736

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Decomposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Flow
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Lifts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Graph
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Sectors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Induced
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Budgets
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_IndexedDecoder
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
set_option autoImplicit false
noncomputable section
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26DecodingGraph
open MultiscaleDecoder
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXDecoderAdapter.rxDegreeZero_parent (x : (state S i.val).presentation.X)
    (v : DoubleCylinderVertex (state S i.val).presentation x S) :
    parent S (i.val+1) (Vertex.x (rxDegreeZeroEquiv S depth i h ⟨x,v⟩)) =
      some (Vertex.x x) := by sorry
