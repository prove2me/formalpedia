-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660
-- name    : P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:13.027003+00:00
-- url     : https://prove2.me/theorems/b446364e-4d49-4c70-abc1-2234010212ff
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Fibre Bound trdeg le 5ed0a4f11660: P2 M Ground Theory Heights  Heights Dominant Fibre Bound trdeg le 5ed0a4f11660
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Fibre Bound trdeg le 5ed0a4f11660 construction uses the P2 M Ground Theory Heights  Heights Dominant Fibre Bound trdeg le 5ed0a4f11660 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDominantFibreBound.lean#L11-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PDominantFibreBound.lean#L11-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
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
open MvPolynomial ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660 {n d : ℕ} (P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime]
    (A : Matrix (Fin d) (Fin n) ℂ) (hA : IsFiniteProjection P A) :
    Algebra.trdeg ℂ (MvPolynomial (Fin n) ℂ ⧸ P) ≤ Cardinal.mk (Fin d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantFibreBound».«trdeg_le» := P2M_GroundTheory_Heights__Heights_DominantFibreBound_trdeg_le_5ed0a4f11660
