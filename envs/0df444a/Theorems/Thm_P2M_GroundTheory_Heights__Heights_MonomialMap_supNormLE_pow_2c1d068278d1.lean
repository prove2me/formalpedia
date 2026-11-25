-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:50:04.728684+00:00
-- url     : https://prove2.me/theorems/664d04fe-7980-45bf-83ee-3cfe214c1e47
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE pow 2c1d068278d1: P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE pow 2c1d068278d1
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE pow 2c1d068278d1 construction uses the P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE pow 2c1d068278d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L92-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L92-L107

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1 (A : HermLine n) (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C)
    (m : ℕ) : IntegralSection.SupNormLE (A.pow m) (s.pow m) (m * C) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«supNormLE_pow» := P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_pow_2c1d068278d1
