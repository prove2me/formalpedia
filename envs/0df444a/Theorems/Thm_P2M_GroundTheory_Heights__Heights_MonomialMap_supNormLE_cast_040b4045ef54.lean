-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54
-- name    : P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:29.210696+00:00
-- url     : https://prove2.me/theorems/2a3d7c33-e341-59fb-95df-e15d032b9687
-- title:
--   P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE cast 040b4045ef54: P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE cast 040b4045ef54
-- statement:
--   The P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE cast 040b4045ef54 construction uses the P2 M Ground Theory Heights  Heights Monomial Map sup Norm LE cast 040b4045ef54 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/EvalConeChartMonomialNeZeroAlt.lean#L109-L117

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

theorem P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54 (A B : HermLine n) (hdeg : A.deg = B.deg) (hmet : ∀ z, A.metric z = B.metric z)
    (s : IntegralSection P A.deg) {C : ℝ} (hs : s.SupNormLE A C) :
    (s.cast hdeg).SupNormLE B C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MonomialMap».«supNormLE_cast» := P2M_GroundTheory_Heights__Heights_MonomialMap_supNormLE_cast_040b4045ef54
