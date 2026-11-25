-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:44.04288+00:00
-- url     : https://prove2.me/theorems/297d37b6-ecad-489f-bbc4-c63bae22cc6b
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg fun Field 2422b22669ab: P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg fun Field 2422b22669ab
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg fun Field 2422b22669ab construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie trdeg fun Field 2422b22669ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L27-L35

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
open scoped IntermediateField.algebraAdjoinAdjoin

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab (y : Fin (N + 1) → Ω) :
    trdeg k (funField (k := k) y) = trdeg k (ratioRing (k := k) y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«trdeg_funField» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_trdeg_funField_2422b22669ab
