-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:29:37.477745+00:00
-- url     : https://prove2.me/theorems/4982a499-725f-4d9e-9693-fcab9ec8c41a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof int Num L cons eq snoc d16d0916dd87: P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof int Num L cons eq snoc
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof int Num L cons eq snoc d16d0916dd87 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Flag Bundle Cut Proof int Num L cons eq snoc d16d0916dd87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleCut.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagBundleCut.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleCut
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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {F : Type} [Field F] (P : Ideal (MRing ι F)) (x : K → ℤ)
    (L : List (K → ℤ)) :
    intNumL F P (x :: L) = intNum F P (Fin.snoc (α := fun _ => K → ℤ) L.get x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«FlagBundleCutProof».«intNumL_cons_eq_snoc» := P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87
