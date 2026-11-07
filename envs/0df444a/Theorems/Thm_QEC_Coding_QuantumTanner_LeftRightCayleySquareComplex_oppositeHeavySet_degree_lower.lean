-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_oppositeHeavySet_degree_lower
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_degree_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:54:27.384045+00:00
-- url     : https://prove2.me/theorems/9caacfeb-16c6-41ec-a7f8-49ce070b7bcc
-- title:
--   Left Right Cayley Square Complex: opposite Heavy Set degree lower
-- statement:
--   A vertex reached by a heavy edge has the source's claimed support degree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L331-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/HeavyEdges.lean#L331-L353

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

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.oppositeHeavySet_degree_lower
    (X : LeftRightCayleySquareComplex G A B Square) (hX : X.HasCayleyLinkIdentities)
    (side : Bool) (x : Word (ZMod 2) Square) (cutoff : Nat) (normal : Finset G)
    (h : G) (hh : h ∈ X.oppositeHeavySet side x cutoff normal) :
    cutoff ≤ ∑ g ∈ X.activeVerticesOnSide side x, X.unionCayleyGraph h g := by sorry
