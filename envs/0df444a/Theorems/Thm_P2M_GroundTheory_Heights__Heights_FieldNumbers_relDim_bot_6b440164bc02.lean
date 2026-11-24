-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:17.275947+00:00
-- url     : https://prove2.me/theorems/6797beb7-34a5-4e32-b4a3-937499b29452
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers rel Dim bot 6b440164bc02: P2 M Ground Theory Heights  Heights Field Numbers rel Dim bot 6b440164bc02
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers rel Dim bot 6b440164bc02 construction uses the P2 M Ground Theory Heights  Heights Field Numbers rel Dim bot 6b440164bc02 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L13-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02 {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {F : Type*} [Field F] :
    relDim (⊥ : Ideal (MRing ι F)) =
      (((Fintype.card (Σ k, ι k) : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«relDim_bot» := P2M_GroundTheory_Heights__Heights_FieldNumbers_relDim_bot_6b440164bc02
