-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:24.045742+00:00
-- url     : https://prove2.me/theorems/dd30c047-74c2-51f1-9375-7ec10885ceaf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom injective aa61db869d27: P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom injective aa61db869d27
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom injective aa61db869d27 construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie rehom injective aa61db869d27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L70-L72

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
include hi₀

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27 : Function.Injective (rehom (k := k) y i₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«rehom_injective» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_rehom_injective_aa61db869d27
