-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea
-- name    : P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:16:19.331977+00:00
-- url     : https://prove2.me/theorems/b88e7adb-20a3-4686-91dc-95e6ecd0a8c9
-- title:
--   P2 M Ground Theory Heights  Heights Chow Height Cycle Eq arch Of Places embedding 2ed4d34525ea: P2 M Ground Theory Heights  Heights Chow Height Cycle Eq arch Of Places embedding 2ed4d34525ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Chow Height Cycle Eq arch Of Places embedding 2ed4d34525ea construction uses the P2 M Ground Theory Heights  Heights Chow Height Cycle Eq arch Of Places embedding 2ed4d34525ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ArchOfPlacesEmbedding.lean#L106-L110

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea {K : Type} [Field K] [NumberField K]
    (N : InfinitePlace K → HermNorm n)
    (hN : ∀ w : InfinitePlace K, w.IsReal → ∀ u, (N w).norm (star u) = (N w).norm u)
    (w : InfinitePlace K) : (archOfPlaces N hN).normAt w.embedding = N w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChowHeightCycleEq».«archOfPlaces_embedding» := P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_archOfPlaces_embedding_2ed4d34525ea
