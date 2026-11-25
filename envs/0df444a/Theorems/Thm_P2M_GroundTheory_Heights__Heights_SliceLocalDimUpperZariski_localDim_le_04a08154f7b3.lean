-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_localDim_le_04a08154f7b3
-- name    : P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_localDim_le_04a08154f7b3
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:38:22.887794+00:00
-- url     : https://prove2.me/theorems/72e0f1ce-645c-4c07-93fe-63570a33fb70
-- title:
--   P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski local Dim le 04a08154f7b3: P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski local Dim le 04a08154f7b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski local Dim le 04a08154f7b3 construction uses the P2 M Ground Theory Heights  Heights Slice Local Dim Upper Zariski local Dim le 04a08154f7b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L30-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLocalDimUpperZariski.lean#L30-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLocalDimUpperZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionsContainOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLeadIdealDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLinearFormCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLocalDimUpperZariski
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
open MvPolynomial Matrix ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_localDim_le_04a08154f7b3 {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (q : Fin n → ℂ) (hq : q ∈ zeroSet I) :
    ringKrullDim (localRingAt I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLocalDimUpperZariski».«localDim_le» := P2M_GroundTheory_Heights__Heights_SliceLocalDimUpperZariski_localDim_le_04a08154f7b3
