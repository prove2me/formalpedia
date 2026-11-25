-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_sum_smul_b83e174a1515
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_sum_smul_b83e174a1515
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:37.686453+00:00
-- url     : https://prove2.me/theorems/9b3089d2-cac9-495d-bd03-62c271d2d261
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At sum smul b83e174a1515: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At sum smul b83e174a1515
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At sum smul b83e174a1515 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At sum smul b83e174a1515 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L35-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsStabilizerLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PHermAtPlace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PGramAtData
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_sum_smul_b83e174a1515 (v : Basis ι E W) {κ : Type*} [Fintype κ] (c : κ → E) (u : κ → W)
    (w : InfinitePlace E) :
    vecAt v (∑ k, c k • u k) w = colMat v u w *ᵥ fun k => w.embedding (c k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«vecAt_sum_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_sum_smul_b83e174a1515
