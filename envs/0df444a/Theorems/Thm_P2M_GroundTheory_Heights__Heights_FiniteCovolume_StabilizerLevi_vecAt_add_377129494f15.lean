-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_add_377129494f15
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_add_377129494f15
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:28:54.309804+00:00
-- url     : https://prove2.me/theorems/b31c2e50-c810-4e46-8d02-4129fcda23e7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At add 377129494f15: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At add 377129494f15
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At add 377129494f15 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At add 377129494f15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_add_377129494f15 (v : Basis ι E W) (x y : W) (w : InfinitePlace E) :
    vecAt v (x + y) w = vecAt v x w + vecAt v y w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«vecAt_add» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_add_377129494f15
