-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:51.697951+00:00
-- url     : https://prove2.me/theorems/c15f2cb2-7604-49e2-b3cb-35fd99931099
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume line Coeffs inv smul 46e4714a8745: P2 M Ground Theory Heights  Heights Finite Covolume line Coeffs inv smul 46e4714a8745
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume line Coeffs inv smul 46e4714a8745 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume line Coeffs inv smul 46e4714a8745 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L34-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L34-L38

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745 (g : h.unitaryGroup) (La : AddSubgroup W) (x : W) :
    lineCoeffs (E := E) (g⁻¹ • La) x = lineCoeffs (E := E) La (g • x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«lineCoeffs_inv_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_lineCoeffs_inv_smul_46e4714a8745
