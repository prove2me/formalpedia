-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:53:43.846368+00:00
-- url     : https://prove2.me/theorems/d11497dc-ed79-5db2-aa3f-cbd5ebb8aa5b
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE mul 874c88085c03: P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE mul 874c88085c03
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE mul 874c88085c03 construction uses the P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE mul 874c88085c03 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L61-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L61-L90

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03 (A B : HermLine n) (s : IntegralSection P A.deg) (t : IntegralSection P B.deg)
    {C C' : ℝ} (hs : s.SupNormLE A C) (ht : t.SupNormLE B C') :
    IntegralSection.SupNormLE (A.mul B) (s.mul t) (C + C') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«supNormLE_mul» := P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_mul_874c88085c03
