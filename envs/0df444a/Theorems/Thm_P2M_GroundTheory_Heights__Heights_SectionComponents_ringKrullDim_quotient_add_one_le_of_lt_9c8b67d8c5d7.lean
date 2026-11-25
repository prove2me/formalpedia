-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7
-- name    : P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:03:02.20195+00:00
-- url     : https://prove2.me/theorems/e71ed989-fec9-4fb9-94ef-d4263414e537
-- title:
--   P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one le of lt 9c8b67d8c5d7: P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one le
-- statement:
--   The P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one le of lt 9c8b67d8c5d7 construction uses the P2 M Ground Theory Heights  Heights Section Components ring Krull Dim quotient add one le of lt 9c8b67d8c5d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L29-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PSectionComponents.lean#L29-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsSectionComponents
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PSectionComponents
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
open GroundTheory.Heights₂.Heights.SectionComponents
variable {F : Type} [Field F] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7 {W' W : Ideal (MvPolynomial (Fin n) F)}
    [W'.IsPrime] (hlt : W' < W) :
    ringKrullDim (MvPolynomial (Fin n) F ⧸ W) + 1 ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SectionComponents».«ringKrullDim_quotient_add_one_le_of_lt» := P2M_GroundTheory_Heights__Heights_SectionComponents_ringKrullDim_quotient_add_one_le_of_lt_9c8b67d8c5d7
