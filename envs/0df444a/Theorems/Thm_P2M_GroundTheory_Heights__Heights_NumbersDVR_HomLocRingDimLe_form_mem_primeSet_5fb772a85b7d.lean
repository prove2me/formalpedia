-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:27.32467+00:00
-- url     : https://prove2.me/theorems/cb504aff-b962-486e-b809-e36cad820676
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le form mem prime Set 5fb772a85b7d: P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le form mem prime Set 5fb772a85b7d
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le form mem prime Set 5fb772a85b7d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hom Loc Ring Dim Le form mem prime Set 5fb772a85b7d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHomLocRingDimLe.lean#L142-L151

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d (hPW : P ≤ W) {q : Ideal (homLocRing P W)} {s : K → ℕ} {f g : MRing ι R}
    (hf : IsMultiHomog f s) (hg : IsMultiHomog g s) (hgW : g ∉ W)
    (h : ValIn P W q (frac P f / frac P g)) : f ∈ primeSet P W q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HomLocRingDimLe».«form_mem_primeSet» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocRingDimLe_form_mem_primeSet_5fb772a85b7d
