-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_quotient_inf_dim_lt_0ab1cb66b420
-- name    : P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_quotient_inf_dim_lt_0ab1cb66b420
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:41.103802+00:00
-- url     : https://prove2.me/theorems/e6c22f4e-912e-4a41-a540-986673a401eb
-- title:
--   P2 M Ground Theory Heights  Heights Divisor General Point Branches quotient inf dim lt 0ab1cb66b420: P2 M Ground Theory Heights  Heights Divisor General Point Branches quotient inf dim lt 0ab1cb66b420
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor General Point Branches quotient inf dim lt 0ab1cb66b420 construction uses the P2 M Ground Theory Heights  Heights Divisor General Point Branches quotient inf dim lt 0ab1cb66b420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorGeneralPointBranches.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorGeneralPointBranches.lean#L14-L29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorOneComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorGeneralPointBranches
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.DivisorGeneralPointBranches

theorem P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_quotient_inf_dim_lt_0ab1cb66b420 {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorGeneralPointBranches».«quotient_inf_dim_lt» := P2M_GroundTheory_Heights__Heights_DivisorGeneralPointBranches_quotient_inf_dim_lt_0ab1cb66b420
