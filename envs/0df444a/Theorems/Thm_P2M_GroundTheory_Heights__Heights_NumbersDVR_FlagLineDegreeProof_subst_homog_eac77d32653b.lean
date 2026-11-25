-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_subst_homog_eac77d32653b
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_subst_homog_eac77d32653b
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:41.423614+00:00
-- url     : https://prove2.me/theorems/7a042eba-4735-4c81-b327-f7f3eccc65eb
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof subst homog eac77d32653b: P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof subst homog eac77d32653b
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof subst homog eac77d32653b construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Line Degree Proof subst homog eac77d32653b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L94-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagLineDegree.lean#L94-L126

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_subst_homog_eac77d32653b {K : Type*} [DecidableEq K] {ι : K → Type} {M : ℕ} {F : Type*} [CommRing F]
    (m : ℕ) (A : Fin M → MRing ι F) (hA : ∀ l, IsMultiHomog (A l) (fun _ => m))
    {h : MRing (bundleIdx ι M) F} {D : Option K → ℕ} (hh : IsMultiHomog h D) :
    IsMultiHomog (aeval (substVar A) h) (fun k => D (some k) + D none * m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagLineDegreeProof».«subst_homog» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_subst_homog_eac77d32653b
