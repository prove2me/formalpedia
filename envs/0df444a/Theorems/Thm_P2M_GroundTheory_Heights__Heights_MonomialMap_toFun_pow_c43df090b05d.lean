-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:04:32.238601+00:00
-- url     : https://prove2.me/theorems/fdce817c-cc6f-4ceb-b694-794ea6c84beb
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map to Fun pow c43df090b05d: P2 M Ground Theory Heights  Heights Monomial Map to Fun pow c43df090b05d
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map to Fun pow c43df090b05d construction uses the P2 M Ground Theory Heights  Heights Monomial Map to Fun pow c43df090b05d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L123-L125

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d {a : ι → ℤ} (s : IntegralSection P a) (m : ℕ) :
    (s.pow m).toFun = s.toFun ^ m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«toFun_pow» := P2M_GroundTheory_Heights__Heights_MonomialMap_toFun_pow_c43df090b05d
