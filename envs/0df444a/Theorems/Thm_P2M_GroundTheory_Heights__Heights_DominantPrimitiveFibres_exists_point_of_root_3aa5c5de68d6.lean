-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_point_of_root_3aa5c5de68d6
-- name    : P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_point_of_root_3aa5c5de68d6
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:05.440272+00:00
-- url     : https://prove2.me/theorems/29248031-4231-56d3-b89d-fd79fa9de1b5
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists point of root 3aa5c5de68d6: P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists point of root 3aa5c5de68d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists point of root 3aa5c5de68d6 construction uses the P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists point of root 3aa5c5de68d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L47-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L47-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StDominantPrimitiveFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PDominantFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveElementFibres
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PDominantPrimitiveFibres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
open GroundTheory.Heights₂.Heights.DominantPrimitiveFibres

theorem P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_point_of_root_3aa5c5de68d6 {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (ℓ : B') (m : Polynomial R')
    (hdiv : ∀ p : Polynomial R', Polynomial.aeval ℓ p = 0 → m ∣ p) (ev : R' →+* ℂ)
    (hev : Function.Surjective ev) (τ : ℂ) (hτ : (m.map ev).IsRoot τ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = ev ∧ ψ ℓ = τ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantPrimitiveFibres».«exists_point_of_root» := P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_point_of_root_3aa5c5de68d6
