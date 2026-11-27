-- Prove2me | Theorems.Thm_PositivityTheory_ThKEnd_Orth_decomp
-- name    : PositivityTheory.ThKEnd.Orth.decomp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:00:14.119227+00:00
-- url     : https://prove2.me/theorems/194420d2-85b1-41b7-a9ea-33413f257b57
-- title:
--   Orth: decomp
-- statement:
--   The Orth construction uses the decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/OrthogonalDecomposition/Imports.lean#L12-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/OrthogonalDecomposition/Imports.lean#L12-L62

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_OrthogonalDecomposition_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEnd PositivityTheory.ThKEnd.Orth
variable {H P Q : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]

theorem PositivityTheory.ThKEnd.Orth.decomp (ρ : H → Module.End ℂ P) (c : H → Module.End ℂ Q) [Nontrivial P]
    (irr : ∀ N : Submodule ℂ P, (∀ h, ∀ x ∈ N, ρ h x ∈ N) → N = ⊥ ∨ N = ⊤) (R : Submodule ℂ Q) (hR : ∀ h, ∀ x ∈ R, c h x ∈ R)
    {f : Q} (hf : f ∈ R) (hs : f ∈ Submodule.span ℂ (vals ρ c)) :
    ∃ (m : ℕ) (U : Fin m → P →ₗ[ℂ] Q) (ξ : Fin m → P), (∀ i, (∀ h x, U i (ρ h x) = c h (U i x)) ∧ ∀ x, U i x ∈ R) ∧
      f = ∑ i, U i (ξ i) := by sorry
