-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:25.914348+00:00
-- url     : https://prove2.me/theorems/075ef9ad-e0e8-4711-958d-01e126435e67
-- title:
--   P2 M Ground Theory Heights  Heights det gram sum Elim 66edcb621772: P2 M Ground Theory Heights  Heights det gram sum Elim 66edcb621772
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram sum Elim 66edcb621772 construction uses the P2 M Ground Theory Heights  Heights det gram sum Elim 66edcb621772 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L72-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L72-L96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772 {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : m → V) (b q : n → V) (C : Matrix m n ℂ) (hq : ∀ j, q j = b j - ∑ i, C i j • a i)
    (horth : ∀ i j, inner ℂ (a i) (q j) = 0) :
    det (gram ℂ (Sum.elim a b)) = det (gram ℂ a) * det (gram ℂ q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_sumElim» := P2M_GroundTheory_Heights__Heights_det_gram_sumElim_66edcb621772
