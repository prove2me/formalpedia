-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:17.200741+00:00
-- url     : https://prove2.me/theorems/7a2a63ca-9d4b-4aa0-8343-53bfec6c1eec
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt char Zero 4a83caadbcde: P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt char Zero 4a83caadbcde
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt char Zero 4a83caadbcde construction uses the P2 M Ground Theory Heights  Heights Targets Curve Ring Finite Alt char Zero 4a83caadbcde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveRingFinite.lean#L57-L63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Targets.CurveRingFiniteAlt
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (hy : IsHorizontal (mCoordIdeal y)) :
    CharZero Ω := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveRingFiniteAlt».«charZero» := P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde
