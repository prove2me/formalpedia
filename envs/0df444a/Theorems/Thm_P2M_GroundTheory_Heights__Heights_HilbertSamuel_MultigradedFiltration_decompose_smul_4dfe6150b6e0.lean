-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:19.512112+00:00
-- url     : https://prove2.me/theorems/97a45f9e-fd59-4628-aa0d-78149f761311
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration decompose smul 4dfe6150b6e0: P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration decompose smul 4dfe6150
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration decompose smul 4dfe6150b6e0 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Multigraded Filtration decompose smul 4dfe6150b6e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L80-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PMultigradedFiltration.lean#L80-L95

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0 (hM : IsMultigrading ι M piece) (f : MRing ι F) {c : K → ℤ} {x : M}
    (hx : x ∈ piece c) (m : K → ℤ) :
    (DirectSum.decompose piece (f • x) m : M) =
      (∑ d ∈ f.support with c + degZ (Finsupp.weight (blockWeight ι) d) = m,
        monomial d (coeff d f)) • x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«MultigradedFiltration».«decompose_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_MultigradedFiltration_decompose_smul_4dfe6150b6e0
