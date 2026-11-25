-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_basis_bb9bf0d408f7
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_basis_bb9bf0d408f7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:27:06.782318+00:00
-- url     : https://prove2.me/theorems/0d2270bc-7ef7-5d0e-85cb-8f67d58bbbb7
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At basis bb9bf0d408f7: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At basis bb9bf0d408f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At basis bb9bf0d408f7 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi vec At basis bb9bf0d408f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_basis_bb9bf0d408f7 (v : Basis ι E W) (i : ι) (w : InfinitePlace E) :
    vecAt v (v i) w = Pi.single i 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«vecAt_basis» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_vecAt_basis_bb9bf0d408f7
