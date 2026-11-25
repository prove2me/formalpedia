-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053
-- name    : P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:03.092861+00:00
-- url     : https://prove2.me/theorems/be113b54-e43d-4ab7-a0a5-8aa983dc69d9
-- title:
--   P2 M Ground Theory Heights  Heights Component Of Inc Ideal one le ring Krull Dim quot e6e3f847a053: P2 M Ground Theory Heights  Heights Component Of Inc Ideal one le ring Krull Dim quot e6e3f847a053
-- statement:
--   The P2 M Ground Theory Heights  Heights Component Of Inc Ideal one le ring Krull Dim quot e6e3f847a053 construction uses the P2 M Ground Theory Heights  Heights Component Of Inc Ideal one le ring Krull Dim quot e6e3f847a053 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L23-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PComponentOfIncIdeal
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
open MvPolynomial
open GroundTheory.Heights₂.Heights.ComponentOfIncIdeal

theorem P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053 {F : Type} [Field F] {n : ℕ} {W : Ideal (MvPolynomial (Fin n) F)}
    (hW : IsProjPrime W) : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComponentOfIncIdeal».«one_le_ringKrullDim_quot» := P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_one_le_ringKrullDim_quot_e6e3f847a053
