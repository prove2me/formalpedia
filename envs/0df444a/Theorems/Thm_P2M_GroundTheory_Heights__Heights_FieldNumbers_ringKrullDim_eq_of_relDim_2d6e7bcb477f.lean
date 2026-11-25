-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_eq_of_relDim_2d6e7bcb477f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_eq_of_relDim_2d6e7bcb477f
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:58:17.675647+00:00
-- url     : https://prove2.me/theorems/806ed9d5-061b-47d9-83ac-fa81e7850c47
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim eq of rel Dim 2d6e7bcb477f: P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim eq of rel Dim 2d6e7bcb477f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim eq of rel Dim 2d6e7bcb477f construction uses the P2 M Ground Theory Heights  Heights Field Numbers ring Krull Dim eq of rel Dim 2d6e7bcb477f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocalRing.lean#L16-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocalRing.lean#L16-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocalRing
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_eq_of_relDim_2d6e7bcb477f {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ringKrullDim_eq_of_relDim» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ringKrullDim_eq_of_relDim_2d6e7bcb477f
