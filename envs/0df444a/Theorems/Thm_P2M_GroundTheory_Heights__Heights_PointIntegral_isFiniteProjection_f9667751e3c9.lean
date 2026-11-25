-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9
-- name    : P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:14:40.106378+00:00
-- url     : https://prove2.me/theorems/f6fece71-10e3-4d53-8667-6d5c4dc46a8c
-- title:
--   P2 M Ground Theory Heights  Heights Point Integral is Finite Projection f9667751e3c9: P2 M Ground Theory Heights  Heights Point Integral is Finite Projection f9667751e3c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Integral is Finite Projection f9667751e3c9 construction uses the P2 M Ground Theory Heights  Heights Point Integral is Finite Projection f9667751e3c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPointIntegral.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPointIntegral.lean#L27-L44

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

theorem P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9 (p : Fin n → ℂ) (A : Matrix (Fin 0) (Fin n) ℂ) :
    IsFiniteProjection (RingHom.ker (MvPolynomial.eval p)) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointIntegral».«isFiniteProjection» := P2M_GroundTheory_Heights__Heights_PointIntegral_isFiniteProjection_f9667751e3c9
