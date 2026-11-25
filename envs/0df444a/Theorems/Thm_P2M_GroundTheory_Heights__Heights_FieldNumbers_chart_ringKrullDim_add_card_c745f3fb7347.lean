-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_chart_ringKrullDim_add_card_c745f3fb7347
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_chart_ringKrullDim_add_card_c745f3fb7347
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:32.658376+00:00
-- url     : https://prove2.me/theorems/5116de0b-7ddc-410f-b72e-7b59e263044a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers chart ring Krull Dim add card c745f3fb7347: P2 M Ground Theory Heights  Heights Field Numbers chart ring Krull Dim add card c745f3fb7347
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers chart ring Krull Dim add card c745f3fb7347 construction uses the P2 M Ground Theory Heights  Heights Field Numbers chart ring Krull Dim add card c745f3fb7347 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDegZeroLocDim.lean#L33-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocDim
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_chart_ringKrullDim_add_card_c745f3fb7347 (h : MChartTrdeg.Statement.{u}) (Q : Ideal (MRing ι F)) [Q.IsPrime]
    (hQ : IsMultiHomogIdeal Q) (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ Q) :
    ringKrullDim (MRing ι F ⧸ chartIdeal Q u) + Fintype.card K = ringKrullDim (MRing ι F ⧸ Q) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«chart_ringKrullDim_add_card» := P2M_GroundTheory_Heights__Heights_FieldNumbers_chart_ringKrullDim_add_card_c745f3fb7347
