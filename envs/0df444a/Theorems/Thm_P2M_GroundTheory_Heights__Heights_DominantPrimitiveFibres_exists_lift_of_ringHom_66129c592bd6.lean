-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6
-- name    : P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:19.775325+00:00
-- url     : https://prove2.me/theorems/6fc40a80-abfb-492b-a086-47d85eb77dfd
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of ring Hom 66129c592bd6: P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of ring Hom 66129c592bd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of ring Hom 66129c592bd6 construction uses the P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists lift of ring Hom 66129c592bd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L39-L45

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

theorem P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6 {R' B' : Type*} [CommRing R'] [CommRing B'] (f : R' →+* B')
    (hf : f.IsIntegral) (φ : R' →+* ℂ) (hφ : Function.Surjective φ)
    (hker : RingHom.ker f ≤ RingHom.ker φ) :
    ∃ ψ : B' →+* ℂ, ψ.comp f = φ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantPrimitiveFibres».«exists_lift_of_ringHom» := P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_lift_of_ringHom_66129c592bd6
