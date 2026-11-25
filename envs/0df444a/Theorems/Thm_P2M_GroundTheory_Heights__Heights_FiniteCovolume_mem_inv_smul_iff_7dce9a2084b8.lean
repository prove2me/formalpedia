-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:56.48686+00:00
-- url     : https://prove2.me/theorems/4f324b75-888c-45a3-9456-62239d8d2e20
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume mem inv smul iff 7dce9a2084b8: P2 M Ground Theory Heights  Heights Finite Covolume mem inv smul iff 7dce9a2084b8
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume mem inv smul iff 7dce9a2084b8 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume mem inv smul iff 7dce9a2084b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L28-L32

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8 {g : h.unitaryGroup} {La : AddSubgroup W} {x : W} :
    x ∈ g⁻¹ • La ↔ g • x ∈ La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«mem_inv_smul_iff» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_inv_smul_iff_7dce9a2084b8
