-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9
-- name    : P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:15:07.442003+00:00
-- url     : https://prove2.me/theorems/996f84be-214e-434c-95b5-ae85f35f510d
-- title:
--   P2 M Ground Theory Heights  Heights Point Slice Mass line sup eq ker 6fb74c079fa9: P2 M Ground Theory Heights  Heights Point Slice Mass line sup eq ker 6fb74c079fa9
-- statement:
--   The P2 M Ground Theory Heights  Heights Point Slice Mass line sup eq ker 6fb74c079fa9 construction uses the P2 M Ground Theory Heights  Heights Point Slice Mass line sup eq ker 6fb74c079fa9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPointSliceMass.lean#L30-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPointSliceMass.lean#L30-L78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PPointChowForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPointIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPointSliceMass
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
open GroundTheory.Heights₂.Heights.PointSliceMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9 (y ℓ : Fin n → ℂ) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : ∀ q, q ∈ J ↔ ∀ t : ℂ, eval (t • y) q = 0) (hc0 : ∑ a, ℓ a * y a ≠ 0) :
    J ⊔ Ideal.span {linForm ℓ - 1} =
      RingHom.ker (MvPolynomial.eval ((∑ a, ℓ a * y a)⁻¹ • y)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«PointSliceMass».«line_sup_eq_ker» := P2M_GroundTheory_Heights__Heights_PointSliceMass_line_sup_eq_ker_6fb74c079fa9
