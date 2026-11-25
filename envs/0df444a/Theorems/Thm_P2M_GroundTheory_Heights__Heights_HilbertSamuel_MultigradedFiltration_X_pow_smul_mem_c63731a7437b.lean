-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:19:35.096433+00:00
-- url     : https://prove2.me/theorems/9ec88775-f4cc-4c38-8166-ec85153c9808
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration X pow smul mem c63731a7437b: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration X pow smul mem c63731a7
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration X pow smul mem c63731a7437b construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration X pow smul mem c63731a7437b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L34-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L34-L46

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b (hM : IsMultigrading ι M piece) (v : Σ k, ι k) (n : ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      ((X v : MRing ι F) ^ n) • x ∈ piece (m + degZ (n • blockWeight ι v)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«X_pow_smul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_X_pow_smul_mem_c63731a7437b
