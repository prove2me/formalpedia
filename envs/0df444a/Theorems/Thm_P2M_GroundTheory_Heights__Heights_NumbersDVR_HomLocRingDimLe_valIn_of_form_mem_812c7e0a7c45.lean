-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:08.086563+00:00
-- url     : https://prove2.me/theorems/73ef8208-9a35-4bd8-983f-39bb751d4336
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In of form mem 812c7e0a7c45: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In of form mem 812c7e0a7c45
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In of form mem 812c7e0a7c45 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le val In of form mem 812c7e0a7c45 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L153-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHomLocRingDimLe
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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocRingDimLe
variable {R : Type u} [CommRing R] {K : Type} [DecidableEq K] {ι : K → Type}
variable (P W : Ideal (MRing ι R)) [P.IsPrime]
variable {P W}
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45 {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W) (h : f ∈ primeSet P W q) :
    ValIn P W q (frac P f / frac P g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«valIn_of_form_mem» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_valIn_of_form_mem_812c7e0a7c45
