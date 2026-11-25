-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:54:37.11927+00:00
-- url     : https://prove2.me/theorems/cad40420-96ab-5693-94d3-2ebca7cc53fb
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume finite sandwich bc5e518da275: P2 M Ground Theory Heights  Heights Finite Covolume finite sandwich bc5e518da275
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume finite sandwich bc5e518da275 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume finite sandwich bc5e518da275 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L31-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLinePairOrbitsFinite.lean#L31-L82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsComplementExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsAdaptedReduction
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLinePairOrbitsFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
open scoped Pointwise
noncomputable section
universe u
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
variable [NoZeroSMulDivisors ℕ A]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275 (M : AddSubgroup A) {n : ℕ} (hn : 0 < n) :
    {L : AddSubgroup A | M ≤ L ∧ (∀ x ∈ L, n • x ∈ M) ∧ L.FG}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«finite_sandwich» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_finite_sandwich_bc5e518da275
