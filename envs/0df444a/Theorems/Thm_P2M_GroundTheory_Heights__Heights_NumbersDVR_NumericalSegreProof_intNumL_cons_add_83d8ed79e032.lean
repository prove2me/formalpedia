-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:09:04.917746+00:00
-- url     : https://prove2.me/theorems/75c95187-3185-48cc-8b1f-34da8ee6976c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L cons add 83d8ed79e032: P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L cons add 83d8ed79
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L cons add 83d8ed79e032 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Numerical Segre Proof int Num L cons add 83d8ed79e032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L162-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PNumericalSegre.lean#L162-L176

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032 (hadd : FieldNumbers.IntNumAdd.Statement.{0}) (F : Type) [Field F]
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P) (l : List (K → ℤ))
    (hd : FieldNumbers.relDim P = ((l.length + 1 : ℕ) : WithBot (WithTop ℤ))) (c c' : K → ℤ) :
    intNumL F P ((c + c') :: l) = intNumL F P (c :: l) + intNumL F P (c' :: l) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«NumericalSegreProof».«intNumL_cons_add» := P2M_GroundTheory_Heights__Heights_NumbersDVR_NumericalSegreProof_intNumL_cons_add_83d8ed79e032
