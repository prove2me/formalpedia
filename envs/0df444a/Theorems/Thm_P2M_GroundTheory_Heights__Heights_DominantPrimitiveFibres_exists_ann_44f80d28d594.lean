-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_ann_44f80d28d594
-- name    : P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_ann_44f80d28d594
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:17:32.236196+00:00
-- url     : https://prove2.me/theorems/5594eaa6-7117-4309-8042-53a6c70d0be7
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists ann 44f80d28d594: P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists ann 44f80d28d594
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists ann 44f80d28d594 construction uses the P2 M Ground Theory Heights  Heights Dominant Primitive Fibres exists ann 44f80d28d594 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L109-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L109-L128

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

theorem P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_ann_44f80d28d594 (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) (b : MvPolynomial (Fin n) ℂ ⧸ Q) :
    letI : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ Q) := (projHom Q A).toRingHom.toAlgebra
    ∃ g : Polynomial (MvPolynomial (Fin d) ℂ), g ≠ 0 ∧ Polynomial.aeval b g = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantPrimitiveFibres».«exists_ann» := P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_exists_ann_44f80d28d594
