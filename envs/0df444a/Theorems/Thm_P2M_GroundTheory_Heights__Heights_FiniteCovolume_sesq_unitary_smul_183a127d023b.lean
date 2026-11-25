-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:04.51759+00:00
-- url     : https://prove2.me/theorems/beacfa14-6e02-5509-b454-51f340c6b39f
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume sesq unitary smul 183a127d023b: P2 M Ground Theory Heights  Heights Finite Covolume sesq unitary smul 183a127d023b
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume sesq unitary smul 183a127d023b construction uses the P2 M Ground Theory Heights  Heights Finite Covolume sesq unitary smul 183a127d023b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L21-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsHyperbolicPairs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StLineNormalForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StComplementLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PAdaptedReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W]
variable {h : HermitianForm F E W}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b (g : h.unitaryGroup) (x y : W) :
    h.toSesq (g • x) (g • y) = h.toSesq x y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«sesq_unitary_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_sesq_unitary_smul_183a127d023b
