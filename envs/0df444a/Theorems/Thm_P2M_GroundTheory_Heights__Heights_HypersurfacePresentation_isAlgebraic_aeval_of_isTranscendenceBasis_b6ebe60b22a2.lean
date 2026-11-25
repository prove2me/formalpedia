-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2
-- name    : P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:51.311054+00:00
-- url     : https://prove2.me/theorems/df1c738d-f776-453a-b18b-2975e74bc99b
-- title:
--   P2 M Ground Theory Heights  Heights Hypersurface Presentation is Algebraic aeval of is Transcendence Basis b6ebe60b22a2: P2 M Ground Theory Heights  Heights Hypersurface Presentation is Algebraic aeva
-- statement:
--   The P2 M Ground Theory Heights  Heights Hypersurface Presentation is Algebraic aeval of is Transcendence Basis b6ebe60b22a2 construction uses the P2 M Ground Theory Heights  Heights Hypersurface Presentation is Algebraic aeval of is Transcendence Basis b6ebe60b22a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L175-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean#L175-L187

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
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
open GroundTheory.Heights₂.Heights.HypersurfacePresentation

theorem P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2 {S A : Type} [CommRing S] [Nontrivial S] [CommRing A]
    [Algebra S A] {d : ℕ} {y : Fin d → A} (hb : IsTranscendenceBasis S y) :
    letI := (MvPolynomial.aeval (R := S) y).toRingHom.toAlgebra
    Algebra.IsAlgebraic (MvPolynomial (Fin d) S) A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HypersurfacePresentation».«isAlgebraic_aeval_of_isTranscendenceBasis» := P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_isAlgebraic_aeval_of_isTranscendenceBasis_b6ebe60b22a2
