-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d
-- name    : P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:36.753803+00:00
-- url     : https://prove2.me/theorems/87ff9daa-d92c-4f04-a4f4-d2b462e262c1
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of is Integral 7e7da0323e6d: P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of is Integral 7e7da032
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of is Integral 7e7da0323e6d construction uses the P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of is Integral 7e7da0323e6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L15-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L15-L37

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

theorem P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d {R' B' : Type*} [CommRing R'] [CommRing B'] [Algebra R' B']
    [Algebra.IsIntegral R' B'] (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker (algebraMap R' B') ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp (algebraMap R' B') = φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantPrimitiveFibres».«exists_lift_of_isIntegral» := P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_isIntegral_7e7da0323e6d
