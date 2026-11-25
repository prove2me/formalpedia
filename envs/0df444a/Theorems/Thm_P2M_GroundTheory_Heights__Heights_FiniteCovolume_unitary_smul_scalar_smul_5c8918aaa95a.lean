-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:00.660541+00:00
-- url     : https://prove2.me/theorems/4eb7320d-a891-5e76-8a5b-5432a8785f7e
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume unitary smul scalar smul 5c8918aaa95a: P2 M Ground Theory Heights  Heights Finite Covolume unitary smul scalar smul 5c8918aaa95a
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume unitary smul scalar smul 5c8918aaa95a construction uses the P2 M Ground Theory Heights  Heights Finite Covolume unitary smul scalar smul 5c8918aaa95a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L25-L26

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a (g : h.unitaryGroup) (a : E) (x : W) : g • (a • x) = a • (g • x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«unitary_smul_scalar_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_unitary_smul_scalar_smul_5c8918aaa95a
