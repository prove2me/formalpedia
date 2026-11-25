-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:38.676275+00:00
-- url     : https://prove2.me/theorems/fe944c01-0a22-43ee-bb78-b2290a289e89
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration homog smul mem 798312d8528d: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration homog smul mem 798312d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration homog smul mem 798312d8528d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration homog smul mem 798312d8528d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L63-L74

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d (hM : IsMultigrading ι M piece) {f : MRing ι F} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (blockWeight ι) f b) {m : K → ℤ} {x : M} (hx : x ∈ piece m) :
    f • x ∈ piece (m + degZ b) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«homog_smul_mem» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_homog_smul_mem_798312d8528d
