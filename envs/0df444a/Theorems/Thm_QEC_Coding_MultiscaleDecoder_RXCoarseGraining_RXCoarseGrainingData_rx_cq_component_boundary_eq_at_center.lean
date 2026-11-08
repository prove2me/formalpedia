-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RXCoarseGraining_RXCoarseGrainingData_rx_cq_component_boundary_eq_at_center
-- name    : QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_cq_component_boundary_eq_at_center
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:03:21.448278+00:00
-- url     : https://prove2.me/theorems/f5429415-3860-4e54-9f82-acbf5d48b43c
-- title:
--   RXCoarse Graining Data: rx cq component boundary eq at center
-- statement:
--   The RXCoarse Graining Data construction uses the rx cq component boundary eq at center property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L1965-L2038
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RXCoarseGraining.lean#L1965-L2038

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXLocalCleaning
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
open QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData
variable {D : BDL26DecoderData depth C0 C1 C2} {i : StepIndex depth}
variable {X Q Z : Type v} [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] [Fintype Z] [DecidableEq Z]
variable {X0 : X → Type u} {Q0 : Q → Type u}
variable {Z0 : Z → Type u} {Z1 : Z → Type u} {Z2 : Z → Type u}
variable [∀ x, Fintype (X0 x)] [∀ q, Fintype (Q0 q)]
variable [∀ z, Fintype (Z0 z)] [∀ z, Fintype (Z1 z)] [∀ z, Fintype (Z2 z)]
variable {Lx : LocalComplexData X (C2 i.succ) (C1 i.succ)}
variable {Lq : LocalComplexData Q (C2 i.succ) (C1 i.succ)}
variable {Lz : LocalComplexData Z (C2 i.succ) (C1 i.succ)}
variable (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
  (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2) D i Lx Lq Lz)

theorem QEC.Coding.MultiscaleDecoder.RXCoarseGraining.RXCoarseGrainingData.rx_cq_component_boundary_eq_at_center
    (A : RXCoarseGrainingData (X := X) (Q := Q) (Z := Z)
      (X0 := X0) (Q0 := Q0) (Z0 := Z0) (Z1 := Z1) (Z2 := Z2)
      D i Lx Lq Lz)
    (sigma tau : D.family.Cochain2 i.succ) (q : Q)
    (p : C2 i.succ) (center : RXVertex X Q Z)
    (hpQnot : p ∉ Lq.syndromeRegion q)
    (hTop : A.topCenter p = center)
    (hAgree : rxSignalAgreementWithin A center 2 sigma tau) :
    D.family.coboundary1 i.succ (cqComponentTotal A sigma q) p =
      D.family.coboundary1 i.succ (cqComponentTotal A tau q) p := by sorry
