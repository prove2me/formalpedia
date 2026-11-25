-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:39.787126+00:00
-- url     : https://prove2.me/theorems/e6737146-a6d4-4fe7-be2c-397096311f9a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume dual Lattice inv smul 6bc15559e293: P2 M Ground Theory Heights  Heights Finite Covolume dual Lattice inv smul 6bc15559e293
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume dual Lattice inv smul 6bc15559e293 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume dual Lattice inv smul 6bc15559e293 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L40-L54

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293 (g : h.unitaryGroup) (La : AddSubgroup W) :
    dualLattice h (g⁻¹ • La) = g⁻¹ • dualLattice h La := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«dualLattice_inv_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_dualLattice_inv_smul_6bc15559e293
