-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:50.210405+00:00
-- url     : https://prove2.me/theorems/3319f5e4-d184-5569-abd6-f43f80170f6a
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map to Fun mul 7d1beff2f443: P2 M Ground Theory Heights  Heights Monomial Map to Fun mul 7d1beff2f443
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map to Fun mul 7d1beff2f443 construction uses the P2 M Ground Theory Heights  Heights Monomial Map to Fun mul 7d1beff2f443 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L119-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L119-L121

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZeroAlt
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.MonomialMap
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable {P : ArithVariety n}

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443 {a b : ι → ℤ} (s : IntegralSection P a) (t : IntegralSection P b) :
    (s.mul t).toFun = s.toFun * t.toFun := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«toFun_mul» := P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_mul_7d1beff2f443
