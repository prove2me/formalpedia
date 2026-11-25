-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_coord_ne_zero_28a40751c75c
-- name    : P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_coord_ne_zero_28a40751c75c
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:15:22.988772+00:00
-- url     : https://prove2.me/theorems/48b07e27-7d47-43ff-8343-42a0d2074755
-- title:
--   P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective coord ne zero 28a40751c75c: P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective coord ne zero 28a40751
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective coord ne zero 28a40751c75c construction uses the P2 M Ground Theory Heights  Heights Targets Curve Vertical Point Injective coord ne zero 28a40751c75c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointInj.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PCurveVertPointInj.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveVertPointLengthSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveVertPointInj
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointInjective
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_coord_ne_zero_28a40751c75c (y : (Σ k, ι k) → Ω) (p : Σ k, ι k)
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«CurveVerticalPointInjective».«coord_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_CurveVerticalPointInjective_coord_ne_zero_28a40751c75c
