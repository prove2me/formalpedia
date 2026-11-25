-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:24.760653+00:00
-- url     : https://prove2.me/theorems/b776ba60-2d46-59f2-a3a9-470ac4d9da1d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom comp dehom 238d65ec5abd: P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom comp dehom 238d65ec5abd
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom comp dehom 238d65ec5abd construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom comp dehom 238d65ec5abd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L74-L80

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
variable (y : Fin (N + 1) → Ω) {i₀ : Fin (N + 1)} (hi₀ : y i₀ ≠ 0)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd : (rehom (k := k) y i₀).comp (dehom y hi₀) = cone (S := k) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«rehom_comp_dehom» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_comp_dehom_238d65ec5abd
