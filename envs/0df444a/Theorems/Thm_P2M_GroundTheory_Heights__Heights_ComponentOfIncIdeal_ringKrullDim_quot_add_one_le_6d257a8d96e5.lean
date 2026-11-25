-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5
-- name    : P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:28:00.869112+00:00
-- url     : https://prove2.me/theorems/a305f67e-97a5-4cb5-bbab-cf28a49bb5b2
-- title:
--   P2 M Ground Theory Heights  Heights Component Of Inc Ideal ring Krull Dim quot add one le 6d257a8d96e5: P2 M Ground Theory Heights  Heights Component Of Inc Ideal ring Krull Dim quot add one le 6d257a
-- statement:
--   The P2 M Ground Theory Heights  Heights Component Of Inc Ideal ring Krull Dim quot add one le 6d257a8d96e5 construction uses the P2 M Ground Theory Heights  Heights Component Of Inc Ideal ring Krull Dim quot add one le 6d257a8d96e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PComponentOfIncIdeal.lean#L12-L21

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

theorem P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5 {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (hPQ : P ≤ Q) (hne : P ≠ Q) : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComponentOfIncIdeal».«ringKrullDim_quot_add_one_le» := P2M_GroundTheory_Heights__Heights_ComponentOfIncIdeal_ringKrullDim_quot_add_one_le_6d257a8d96e5
