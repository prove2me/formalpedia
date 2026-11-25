-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:19:05.063238+00:00
-- url     : https://prove2.me/theorems/61b25ccb-57a0-45ea-89f4-dd6e62469039
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists step 90568b34aa57: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists step 90568b34aa57
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists step 90568b34aa57 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration exists step 90568b34aa57 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L224-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L224-L235

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_LengthLocalizedQuotientEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMultigradedFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u v
open GroundTheory.Heights₂.Heights.HilbertSamuel.MultigradedFiltration
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
variable [DecidableEq (K → ℤ)] [DirectSum.Decomposition piece]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57 (hM : IsMultigrading ι M piece) {N : Submodule (MRing ι F) M}
    (hN : IsGradedSub piece N) (hNt : N ≠ ⊤) :
    ∃ (c : K → ℤ) (x : M), x ∈ piece c ∧ x ∉ N ∧ (N.colon {x}).IsPrime ∧
      IsMultiHomogIdeal (N.colon {x}) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«exists_step» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_exists_step_90568b34aa57
