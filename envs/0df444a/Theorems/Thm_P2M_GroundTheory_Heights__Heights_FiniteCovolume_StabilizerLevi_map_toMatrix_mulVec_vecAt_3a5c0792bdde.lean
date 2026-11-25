-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_map_toMatrix_mulVec_vecAt_3a5c0792bdde
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_map_toMatrix_mulVec_vecAt_3a5c0792bdde
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:37:42.180217+00:00
-- url     : https://prove2.me/theorems/c96f8580-6c6f-4cba-8c1e-38e6265e2061
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi map to Matrix mul Vec vec At 3a5c0792bdde: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi map to Matrix mul Vec
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi map to Matrix mul Vec vec At 3a5c0792bdde construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi map to Matrix mul Vec vec At 3a5c0792bdde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L64-L70

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_map_toMatrix_mulVec_vecAt_3a5c0792bdde (v : Basis ι E W) (f : W →ₗ[E] W) (x : W)
    (w : InfinitePlace E) :
    (LinearMap.toMatrix v v f).map w.embedding *ᵥ vecAt v x w = vecAt v (f x) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«map_toMatrix_mulVec_vecAt» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_map_toMatrix_mulVec_vecAt_3a5c0792bdde
