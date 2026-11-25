-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc
-- name    : P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:50:43.974972+00:00
-- url     : https://prove2.me/theorems/75d8c922-b188-4fcc-9f21-a7b44a408287
-- title:
--   P2 M Ground Theory Heights  Heights trdeg lt of surjective of ker ne bot e46280f334dc: P2 M Ground Theory Heights  Heights trdeg lt of surjective of ker ne bot e46280f334dc
-- statement:
--   The P2 M Ground Theory Heights  Heights trdeg lt of surjective of ker ne bot e46280f334dc construction uses the P2 M Ground Theory Heights  Heights trdeg lt of surjective of ker ne bot e46280f334dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimTrdeg.lean#L9-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IntDimTrdeg.lean#L9-L48

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

theorem P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc {R B C : Type} [CommRing R] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra R B] [Algebra R C] (f : B →ₐ[R] C)
    (hf : Function.Surjective f) (hker : RingHom.ker f ≠ ⊥)
    (hinj : Function.Injective (algebraMap R C)) (hfin : trdeg R B < ℵ₀) :
    trdeg R C < trdeg R B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«trdeg_lt_of_surjective_of_ker_ne_bot» := P2M_GroundTheory_Heights__Heights_trdeg_lt_of_surjective_of_ker_ne_bot_e46280f334dc
