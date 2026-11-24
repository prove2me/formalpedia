-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
-- name    : P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:29.703417+00:00
-- url     : https://prove2.me/theorems/574ba96b-0b0a-4768-b957-eb2323b07907
-- title:
--   P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt gen Index eq 793276f70c85: P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt gen Index eq 793276f70c85
-- statement:
--   The P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt gen Index eq 793276f70c85 construction uses the P2 M Ground Theory Heights  Heights Invertible Ideal Index Alt gen Index eq 793276f70c85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L26-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PInvertibleIdealIndex.lean#L26-L73

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsOrderIdealIndexExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulMemOfSpanEqTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
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
open NumberField
noncomputable section
open GroundTheory.Heights₂.Heights.InvertibleIdealIndexAlt
variable {L : Type} [Field L]

theorem P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85 {X J M : AddSubgroup L} {β δ : L} (hβ : β ≠ 0) (hδ : δ ≠ 0) (hJX : J ≤ X)
    (hβX : X.map (mulBy β) ≤ X) (hδX : X.map (mulBy δ) ≤ X) (hβJ : J.map (mulBy β) ≤ J)
    (hM : ∀ x, x ∈ M ↔ ∃ y ∈ J, β * x = δ * y) (hJ : J.relIndex X ≠ 0)
    (hδ' : (X.map (mulBy δ)).relIndex X ≠ 0) :
    genIndex M X = ((X.map (mulBy β)).relIndex X : ℝ) /
      (((X.map (mulBy δ)).relIndex X : ℝ) * (J.relIndex X : ℝ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«InvertibleIdealIndexAlt».«genIndex_eq» := P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_genIndex_eq_793276f70c85
