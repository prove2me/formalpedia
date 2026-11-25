-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d
-- name    : P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:31.352412+00:00
-- url     : https://prove2.me/theorems/5af649d2-aa6e-5601-85ed-d0852392f612
-- title:
--   P2 M Ground Theory Heights  Heights trdeg zmod quotient le 1b4c4c03bf8d: P2 M Ground Theory Heights  Heights trdeg zmod quotient le 1b4c4c03bf8d
-- statement:
--   The P2 M Ground Theory Heights  Heights trdeg zmod quotient le 1b4c4c03bf8d construction uses the P2 M Ground Theory Heights  Heights trdeg zmod quotient le 1b4c4c03bf8d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimTrdeg.lean#L50-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimTrdeg.lean#L50-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IntDimTrdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Algebra Cardinal MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d {B : Type} [CommRing B] [IsDomain B] [Algebra ℤ B]
    (hinj : Function.Injective (algebraMap ℤ B)) (p : ℕ) [Fact p.Prime] (Q : Ideal B) [Q.IsPrime]
    [CharP (B ⧸ Q) p] :
    letI := ZMod.algebra (B ⧸ Q) p
    trdeg (ZMod p) (B ⧸ Q) ≤ trdeg ℤ B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«trdeg_zmod_quotient_le» := P2M_GroundTheory_Heights__Heights_trdeg_zmod_quotient_le_1b4c4c03bf8d
