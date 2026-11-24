-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveGermComponents_mem_zeroSet_iff_le_ker_1b3406fd666e
-- name    : P2M_GroundTheory_Heights__Heights_CurveGermComponents_mem_zeroSet_iff_le_ker_1b3406fd666e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:46:08.925931+00:00
-- url     : https://prove2.me/theorems/efdb825f-bf1d-488c-8dd5-2cd1cefb14c6
-- title:
--   P2 M Ground Theory Heights  Heights Curve Germ Components mem zero Set iff le ker 1b3406fd666e: P2 M Ground Theory Heights  Heights Curve Germ Components mem zero Set iff le ker 1b3406fd666e
-- statement:
--   The P2 M Ground Theory Heights  Heights Curve Germ Components mem zero Set iff le ker 1b3406fd666e construction uses the P2 M Ground Theory Heights  Heights Curve Germ Components mem zero Set iff le ker 1b3406fd666e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCurveGermComponents.lean#L16-L18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalDimDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveGermComponents
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.CurveGermComponents
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_CurveGermComponents_mem_zeroSet_iff_le_ker_1b3406fd666e (J : Ideal (MvPolynomial (Fin n) ℂ)) (x : Fin n → ℂ) :
    x ∈ zeroSet J ↔ J ≤ RingHom.ker (eval x : MvPolynomial (Fin n) ℂ →+* ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«CurveGermComponents».«mem_zeroSet_iff_le_ker» := P2M_GroundTheory_Heights__Heights_CurveGermComponents_mem_zeroSet_iff_le_ker_1b3406fd666e
