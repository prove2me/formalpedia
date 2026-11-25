-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DivisorBranches_quotient_inf_dim_lt_0a71c29a111f
-- name    : P2M_GroundTheory_Heights__Heights_DivisorBranches_quotient_inf_dim_lt_0a71c29a111f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:06.422629+00:00
-- url     : https://prove2.me/theorems/dbf18e28-a6ef-545b-8e2c-34258d38325e
-- title:
--   P2 M Ground Theory Heights  Heights Divisor Branches quotient inf dim lt 0a71c29a111f: P2 M Ground Theory Heights  Heights Divisor Branches quotient inf dim lt 0a71c29a111f
-- statement:
--   The P2 M Ground Theory Heights  Heights Divisor Branches quotient inf dim lt 0a71c29a111f construction uses the P2 M Ground Theory Heights  Heights Divisor Branches quotient inf dim lt 0a71c29a111f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDivisorBranches.lean#L18-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelExists
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorRegularGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDivisorChartGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPointBranches
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDivisorBranches
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
open GroundTheory.Heights₂.Heights.DivisorBranches

theorem P2M_GroundTheory_Heights__Heights_DivisorBranches_quotient_inf_dim_lt_0a71c29a111f {R : Type*} [CommRing R] {I₁ I₂ : Ideal R} {d : ℕ}
    (h₁ : ringKrullDim (R ⧸ I₁) < (d : ℕ)) (h₂ : ringKrullDim (R ⧸ I₂) < (d : ℕ)) :
    ringKrullDim (R ⧸ (I₁ ⊓ I₂)) < (d : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DivisorBranches».«quotient_inf_dim_lt» := P2M_GroundTheory_Heights__Heights_DivisorBranches_quotient_inf_dim_lt_0a71c29a111f
