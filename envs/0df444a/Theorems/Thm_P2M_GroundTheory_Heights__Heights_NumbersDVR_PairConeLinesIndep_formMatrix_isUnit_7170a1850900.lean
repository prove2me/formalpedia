-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:28.896347+00:00
-- url     : https://prove2.me/theorems/589605bd-6a03-4c9c-b1c8-03e45b786f93
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep form Matrix is Unit 7170a1850900: P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep form Matrix is Unit 7170a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep form Matrix is Unit 7170a1850900 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Pair Cone Lines Indep form Matrix is Unit 7170a1850900 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeLinesIndep.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPairConeLinesIndep.lean#L11-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairConeLinesIndep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairConeLinesIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900 {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {N : ℕ}
    (e : Module.Basis (Fin N) Ω E) (ψ : Fin N → Module.Dual Ω E) (hψ : LinearIndependent Ω ψ) :
    IsUnit (Matrix.of fun i j => ψ i (e j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PairConeLinesIndep».«formMatrix_isUnit» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PairConeLinesIndep_formMatrix_isUnit_7170a1850900
