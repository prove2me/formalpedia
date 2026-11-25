-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T07:53:52.298127+00:00
-- url     : https://prove2.me/theorems/48513b90-375f-493b-9667-10133672fc35
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie aeval C mul X injective c5ce1551daa7: P2 M Ground Theory Heights  Heights Kleiman Dim Tie aeval C mul X injective c5ce1551daa7
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie aeval C mul X injective c5ce1551daa7 construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie aeval C mul X injective c5ce1551daa7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L43-L52

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PDimTie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Algebra Cardinal
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.DimTie
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7 {c : Ω} (hc : c ≠ 0) :
    Function.Injective (Polynomial.aeval (R := Ω) (Polynomial.C c * Polynomial.X)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«aeval_C_mul_X_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_aeval_C_mul_X_injective_c5ce1551daa7
