-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c
-- name    : P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:53.54852+00:00
-- url     : https://prove2.me/theorems/193b6d43-ef11-55a9-ad39-e338c1f5db9c
-- title:
--   P2 M Ground Theory Heights  Heights Dominant Primitive Fibres dim eq 152f4491059c: P2 M Ground Theory Heights  Heights Dominant Primitive Fibres dim eq 152f4491059c
-- statement:
--   The P2 M Ground Theory Heights  Heights Dominant Primitive Fibres dim eq 152f4491059c construction uses the P2 M Ground Theory Heights  Heights Dominant Primitive Fibres dim eq 152f4491059c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L77-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PDominantPrimitiveFibres.lean#L77-L107

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

theorem P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c (hG : GenericProjectionFinite.Statement) {n d : ℕ} (Q : Ideal (MvPolynomial (Fin n) ℂ))
    (A : Matrix (Fin d) (Fin n) ℂ) (hQ : Q.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤ ((d : ℕ) : WithBot ℕ∞))
    (hinj : Function.Injective (projHom Q A)) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) = ((d : ℕ) : WithBot ℕ∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«DominantPrimitiveFibres».«dim_eq» := P2M_GroundTheory_Heights__Heights_DominantPrimitiveFibres_dim_eq_152f4491059c
