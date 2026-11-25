-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_of_isFiniteProjection_d64b99b5e2d4
-- name    : P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_of_isFiniteProjection_d64b99b5e2d4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:41:39.798804+00:00
-- url     : https://prove2.me/theorems/9c58b1de-ee3b-4d71-b5a6-0dc66b6d7d7b
-- title:
--   P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim of is Finite Projection d64b99b5e2d4: P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim of is Finite Projection d64b99b5e2d4
-- statement:
--   The P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim of is Finite Projection d64b99b5e2d4 construction uses the P2 M Ground Theory Heights  Heights Var Int Add ring Krull Dim of is Finite Projection d64b99b5e2d4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarIntAdd.lean#L40-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarIntAdd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarIntAdd
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
open MvPolynomial MeasureTheory ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.VarIntAdd

theorem P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_of_isFiniteProjection_d64b99b5e2d4 {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin k) (Fin n) ℂ} (hA : IsFiniteProjection J A) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarIntAdd».«ringKrullDim_of_isFiniteProjection» := P2M_GroundTheory_Heights__Heights_VarIntAdd_ringKrullDim_of_isFiniteProjection_d64b99b5e2d4
