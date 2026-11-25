-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_init_d69c9fa2d685
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_init_d69c9fa2d685
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:20.428841+00:00
-- url     : https://prove2.me/theorems/c243a7e8-527a-447a-b5bd-ab47b2decdcc
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull init d69c9fa2d685: P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull init d69c9fa2d685
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull init d69c9fa2d685 construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Prefix Pull init d69c9fa2d685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixed.lean#L34-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFVert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter
open GroundTheory.Heights₂.Heights.Targets.ContractMixed
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [∀ k, Fintype (ι' k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_init_d69c9fa2d685 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {p n : ℕ} {L' : Fin (n + 1) → HermLine ι'}
    (h : PrefixPull κ v p L') (hpn : p ≤ n) : PrefixPull κ v p (Fin.init L') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixed».«PrefixPull».«init» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixed_PrefixPull_init_d69c9fa2d685
