-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:31.666293+00:00
-- url     : https://prove2.me/theorems/dc84fdd3-a890-5830-b40d-fa10ee2c80cb
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Dim Tie prime Of eq ker 7df1ef8391e4: P2 M Ground Theory Heights  Heights Kleiman Dim Tie prime Of eq ker 7df1ef8391e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Dim Tie prime Of eq ker 7df1ef8391e4 construction uses the P2 M Ground Theory Heights  Heights Kleiman Dim Tie prime Of eq ker 7df1ef8391e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PDimTie.lean#L82-L85

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4 : primeOf (S := k) y = RingHom.ker (dehom (k := k) y hi₀) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«DimTie».«primeOf_eq_ker» := P2M_GroundTheory_Heights__Heights_Kleiman_DimTie_primeOf_eq_ker_7df1ef8391e4
