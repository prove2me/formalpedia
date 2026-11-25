-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:40.81098+00:00
-- url     : https://prove2.me/theorems/5b8fac17-2335-4484-a42f-916d7df36ea7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration monomial smul mem cf15e5d2941f: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration monomial smul mem cf
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration monomial smul mem cf15e5d2941f construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration monomial smul mem cf15e5d2941f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L48-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L48-L61

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f (hM : IsMultigrading ι M piece) (d : (Σ k, ι k) →₀ ℕ) :
    ∀ (m : K → ℤ) (x : M), x ∈ piece m →
      (monomial d (1 : F) : MRing ι F) • x ∈ piece (m + degZ (Finsupp.weight (blockWeight ι) d)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«monomial_smul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_monomial_smul_mem_cf15e5d2941f
