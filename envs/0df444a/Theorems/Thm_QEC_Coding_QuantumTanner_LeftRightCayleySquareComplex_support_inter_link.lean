-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LeftRightCayleySquareComplex_support_inter_link
-- name    : QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.support_inter_link
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:15:13.432202+00:00
-- url     : https://prove2.me/theorems/1a890bd6-edb5-4944-86c9-4410c0fcb860
-- title:
--   Left Right Cayley Square Complex: support inter link
-- statement:
--   The Left Right Cayley Square Complex construction uses the support inter link property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L57-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Distance.lean#L57-L69

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_CSS_WeightDescent
import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDistance
import Definitions.Def_QEC_Coding_QuantumTanner_Distance
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
open QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex
variable {G A B Square : Type v} [Group G] [Fintype G] [Fintype A] [Fintype B]
  [Fintype Square]

theorem QEC.Coding.QuantumTanner.LeftRightCayleySquareComplex.support_inter_link (X : LeftRightCayleySquareComplex G A B Square)
    (vertex : G × Bool) (x : Word (ZMod 2) Square) :
    hammingSupport x ∩ Finset.univ.image (X.link vertex) =
      (hammingSupport (X.localRestriction vertex x)).image (X.link vertex) := by sorry
