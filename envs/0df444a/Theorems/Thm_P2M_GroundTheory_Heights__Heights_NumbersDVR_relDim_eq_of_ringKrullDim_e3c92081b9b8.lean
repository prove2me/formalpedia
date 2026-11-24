-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:07.601108+00:00
-- url     : https://prove2.me/theorems/ff56393a-129a-42be-b156-23a63c594167
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR rel Dim eq of ring Krull Dim e3c92081b9b8: P2 M Ground Theory Heights  Heights Numbers DVR rel Dim eq of ring Krull Dim e3c92081b9b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR rel Dim eq of ring Krull Dim e3c92081b9b8 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR rel Dim eq of ring Krull Dim e3c92081b9b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumRatSection.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumRatSection.lean#L12-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open GroundTheory.Heights₂.Heights.FieldNumbers
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8 {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} (I : Ideal (MRing ι F)) (n : ℕ)
    (h : ringKrullDim (MRing ι F ⧸ I) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    relDim I = (n : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«relDim_eq_of_ringKrullDim» := P2M_GroundTheory_Heights__Heights_NumbersDVR_relDim_eq_of_ringKrullDim_e3c92081b9b8
