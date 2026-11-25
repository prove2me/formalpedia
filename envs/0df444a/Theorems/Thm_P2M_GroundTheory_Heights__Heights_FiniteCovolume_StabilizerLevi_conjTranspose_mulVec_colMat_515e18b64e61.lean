-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjTranspose_mulVec_colMat_515e18b64e61
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjTranspose_mulVec_colMat_515e18b64e61
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:36:47.05829+00:00
-- url     : https://prove2.me/theorems/565bbd37-dba0-5c89-a1d7-594b0a199638
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi conj Transpose mul Vec col Mat 515e18b64e61: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi conj Transpose mul
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi conj Transpose mul Vec col Mat 515e18b64e61 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi conj Transpose mul Vec col Mat 515e18b64e61 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviPlaces.lean#L49-L51

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjTranspose_mulVec_colMat_515e18b64e61 (v : Basis ι E W) {κ : Type*} [Fintype κ] (u : κ → W)
    (w : InfinitePlace E) (z : ι → ℂ) (k : κ) :
    ((colMat v u w)ᴴ *ᵥ z) k = star (vecAt v (u k) w) ⬝ᵥ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«conjTranspose_mulVec_colMat» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjTranspose_mulVec_colMat_515e18b64e61
