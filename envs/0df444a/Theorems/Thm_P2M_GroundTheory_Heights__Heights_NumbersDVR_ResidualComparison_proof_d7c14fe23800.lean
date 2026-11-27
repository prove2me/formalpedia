-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ResidualComparison_proof_d7c14fe23800
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_ResidualComparison_proof_d7c14fe23800
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:25.589078+00:00
-- url     : https://prove2.me/theorems/c997dfe6-3cc4-5473-8c6c-ee48f2a17842
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Residual Comparison proof d7c14fe23800: P2 M Ground Theory Heights  Heights Numbers DVR Residual Comparison proof d7c14fe23800
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Residual Comparison proof d7c14fe23800 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Residual Comparison proof d7c14fe23800 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsFurther.lean#L12-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/ImportsFurther.lean#L12-L94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTail
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsFurther
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53

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
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_ResidualComparison_proof_d7c14fe23800 (hpieces : BlowUpDecomposition.Statement.{u})
    (hdisj : ResidualDisjoint.Statement.{u}) (hcontr : ResidualContraction.Statement.{u}) :
    ResidualComparison.Statement.{u} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«ResidualComparison».«proof» := P2M_GroundTheory_Heights__Heights_NumbersDVR_ResidualComparison_proof_d7c14fe23800
