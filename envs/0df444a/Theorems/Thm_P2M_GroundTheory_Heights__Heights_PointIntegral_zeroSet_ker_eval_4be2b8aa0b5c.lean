-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c
-- name    : P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:46.969216+00:00
-- url     : https://prove2.me/theorems/7274b93d-135a-4afd-8feb-4450480e88e0
-- title:
--   P2 M Ground Theory Heights  Heights Point Integral zero Set ker eval 4be2b8aa0b5c: P2 M Ground Theory Heights  Heights Point Integral zero Set ker eval 4be2b8aa0b5c
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Integral zero Set ker eval 4be2b8aa0b5c construction uses the P2 M Ground Theory Heights  Heights Point Integral zero Set ker eval 4be2b8aa0b5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPointIntegral.lean#L15-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPointIntegral.lean#L15-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.PointIntegral
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c (p : Fin n → ℂ) :
    zeroSet (RingHom.ker (MvPolynomial.eval p)) = {p} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointIntegral».«zeroSet_ker_eval» := P2M_GroundTheory_Heights__Heights_PointIntegral_zeroSet_ker_eval_4be2b8aa0b5c
