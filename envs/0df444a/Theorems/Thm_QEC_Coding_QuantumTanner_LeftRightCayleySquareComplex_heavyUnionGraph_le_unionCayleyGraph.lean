-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_heavyUnionGraph_le_unionCayleyGraph
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.heavyUnionGraph_le_unionCayleyGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:31:42.55053+00:00
-- url     : https://prove2.me/theorems/3da74e9e-76c3-4b5e-886e-f46857eadf79
-- title:
--   Left Right Cayley Square Complex: heavy Union Graph le union Cayley Graph
-- statement:
--   The Left Right Cayley Square Complex construction uses the heavy Union Graph le union Cayley Graph property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L313-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L313-L323

import Definitions.Def_QEC_Coding_QuantumTanner_CayleyLink
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
import Definitions.Def_QEC_Coding_QuantumTanner_ViewAssembly
import Definitions.Def_QEC_Coding_ExpanderCodes_MixingDegree
import Definitions.Def_QEC_Coding_QuantumTanner_HeavyEdges
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
open Classical QEC.Coding.SmallSetExpansion
universe v
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.heavyUnionGraph_le_unionCayleyGraph
    (X : LeftRightCayleySquareComplex G A B Square) (side : Bool)
    (x : Word (ZMod 2) Square) (cutoff : Nat) (g h : G) :
    X.heavyUnionGraph side x cutoff g h ≤ X.unionCayleyGraph g h := by sorry
