-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_cone_of_isMultiHomog_37528e56c467
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_cone_of_isMultiHomog_37528e56c467
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:30:38.53392+00:00
-- url     : https://prove2.me/theorems/10649404-ec0b-4997-a098-15a9a4f1c59d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof cone of is Multi Homog 37528e56c467: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof cone of is Multi Homo
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof cone of is Multi Homog 37528e56c467 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof cone of is Multi Homog 37528e56c467 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L21-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_cone_of_isMultiHomog_37528e56c467 {K Kt : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {R S : Type*} [CommRing R] [CommRing S] (r : R →+* S)
    (x : (Σ k, ι k) → S) (τ : K → Kt) {h : MRing ι R} {D : K → ℕ} (hh : IsMultiHomog h D) :
    eval₂Hom (C.comp r) (fun p => C (x p) * X (τ p.1)) h =
      C (eval₂ r x h) * ∏ k, (X (τ k) : MvPolynomial Kt S) ^ D k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineDegreeProof».«cone_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_cone_of_isMultiHomog_37528e56c467
