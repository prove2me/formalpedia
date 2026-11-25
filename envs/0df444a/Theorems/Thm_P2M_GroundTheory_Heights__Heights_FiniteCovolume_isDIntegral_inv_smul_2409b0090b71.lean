-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:26.608229+00:00
-- url     : https://prove2.me/theorems/931182c2-9f3f-519e-b7f4-6ecd07070a7a
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume is DIntegral inv smul 2409b0090b71: P2 M Ground Theory Heights  Heights Finite Covolume is DIntegral inv smul 2409b0090b71
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume is DIntegral inv smul 2409b0090b71 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume is DIntegral inv smul 2409b0090b71 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L56-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PAdaptedReduction.lean#L56-L100

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

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71 (g : h.unitaryGroup) {D : ℕ} {La : AddSubgroup W}
    (hLa : IsDIntegral h D La) : IsDIntegral h D (g⁻¹ • La) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«isDIntegral_inv_smul» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_isDIntegral_inv_smul_2409b0090b71
