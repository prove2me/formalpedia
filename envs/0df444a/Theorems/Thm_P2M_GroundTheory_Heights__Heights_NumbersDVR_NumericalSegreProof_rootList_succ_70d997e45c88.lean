-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:53.351047+00:00
-- url     : https://prove2.me/theorems/fa7df5cc-148e-44c0-952e-d087b41c75c5
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List succ 70d997e45c88: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List succ 70d997e45c88
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List succ 70d997e45c88 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof root List succ 70d997e45c88 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L85-L90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PNumericalSegre
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
open GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegreProof
variable {K : Type*} [DecidableEq K]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88 {i : ℕ} (x : Fin (i + 1) → K → ℤ) (α : Fin (i + 1) → ℕ) :
    rootList x α = rootList (fun j => x (Fin.castSucc j)) (Fin.init α) ++
      List.replicate (α (Fin.last i)) (x (Fin.last i)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«rootList_succ» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_rootList_succ_70d997e45c88
