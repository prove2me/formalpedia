-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:26.686707+00:00
-- url     : https://prove2.me/theorems/accf3f91-cb35-4d12-ba8c-b8dde0c22e50
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp mem sup 8b18db97daef: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp mem sup 8b18db97daef
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp mem sup 8b18db97daef construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum comp mem sup 8b18db97daef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L97-L104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsFiltrationHilbSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFiltrationStepHilb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGradedPieceQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PFiltrationHilbSum
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
open GroundTheory.Heights₂.Heights.HilbertSamuel.FiltrationHilbSum
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {M : Type v} [AddCommGroup M] [Module (MRing ι F) M] [Module F M]
  [IsScalarTower F (MRing ι F) M] {piece : (K → ℤ) → Submodule F M}
omit [DecidableEq K] [IsScalarTower F (MRing ι F) M]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef [DirectSum.Decomposition piece] {N₁ N₂ : Submodule (MRing ι F) M}
    (h₁ : ∀ y ∈ N₁, ∀ m, comp (piece := piece) m y ∈ N₁)
    (h₂ : ∀ y ∈ N₂, ∀ m, comp (piece := piece) m y ∈ N₂) :
    ∀ y ∈ N₁ ⊔ N₂, ∀ m, comp (piece := piece) m y ∈ N₁ ⊔ N₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«comp_mem_sup» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_comp_mem_sup_8b18db97daef
