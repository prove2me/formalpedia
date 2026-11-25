-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:00.735404+00:00
-- url     : https://prove2.me/theorems/0cd446b4-bc96-49c5-b636-c6367a81bbc7
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum step 2ad7e30af467: P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum step 2ad7e30af467
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum step 2ad7e30af467 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Filtration Hilb Sum step 2ad7e30af467 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L108-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PFiltrationHilbSum.lean#L108-L243

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
open Classical

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467 [∀ k, Fintype (ι k)] (hM : IsMultigrading ι M piece) [DirectSum.Decomposition piece]
    {N N' : Submodule (MRing ι F) M} {x : M} {c : K → ℤ} {q : Ideal (MRing ι F)}
    (hx : x ∈ piece c) (hN' : N' = N ⊔ Submodule.span (MRing ι F) {x})
    (hq : ∀ s : MRing ι F, s • x ∈ N ↔ s ∈ q)
    (hgr : ∀ y ∈ N, ∀ m, comp (piece := piece) m y ∈ N) (m : K → ℤ)
    [FiniteDimensional F ↥(N.restrictScalars F ⊓ piece m)] :
    FiniteDimensional F ↥(N'.restrictScalars F ⊓ piece m) ∧
      (Module.finrank F ↥(N'.restrictScalars F ⊓ piece m) : ℤ) =
        Module.finrank F ↥(N.restrictScalars F ⊓ piece m) + hilbFn q (m - c) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«FiltrationHilbSum».«step» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_FiltrationHilbSum_step_2ad7e30af467
