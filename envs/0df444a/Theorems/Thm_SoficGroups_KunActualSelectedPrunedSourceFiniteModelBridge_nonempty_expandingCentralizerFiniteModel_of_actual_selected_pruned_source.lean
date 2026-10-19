-- Prove2me | Theorems.Thm_SoficGroups_KunActualSelectedPrunedSourceFiniteModelBridge_nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
-- name    : SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/9eb33689-8012-4593-9ac2-4fd64e3a84e0
-- title:
--   SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise

theorem SoficGroups.KunActualSelectedPrunedSourceFiniteModelBridge.nonempty_expandingCentralizerFiniteModel_of_actual_selected_pruned_source
    {G J : Type} [Group G] [Group J]
    [DecidableEq G]
    (P : SoficGroups.KazhdanPair.{0, 0} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (F : Finset J)
    (W : ℕ → Type)
    [∀ n, Fintype (W n)] [∀ n, DecidableEq (W n)]
    (σ : (n : ℕ) → ↥S → Equiv.Perm (W n))
    (hσone : ∀ n (i : ↥S), (i : G) = 1 → σ n i = 1)
    (p : (n : ℕ) → J → Equiv.Perm (W n))
    (hp : ∀ n, p n 1 = 1)
    (Z : (n : ℕ) → Finset (W n))
    (hZ : ∀ n, (Z n).Nonempty)
    (hlarge : Tendsto (fun n => (Z n).card) atTop atTop)
    (τ : (n : ℕ) → ↥S →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hτ : ∀ n i (x : W n) (hx : x ∈ Z n)
      (_hi : σ n i x ∈ Z n),
        ((τ n i ⟨x, hx⟩ :
          {x : W n // x ∈ Z n}) : W n) = σ n i x)
    (ρ : (n : ℕ) → G →
      Equiv.Perm {x : W n // x ∈ Z n})
    (hρone : ∀ n, ρ n 1 = 1)
    (hρmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (ρ n (a * g)) (ρ n a * ρ n g))
        atTop (𝓝 0))
    (hρgenerator : ∀ i : ↥S,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (τ n i) (ρ n (i : G)))
        atTop (𝓝 0))
    (ell : ℝ) (hell : 0 < ell)
    (hexp : ∀ n, ∀ E : Finset {x : W n // x ∈ Z n},
      ell * min (E.card : ℝ)
        ((Fintype.card {x : W n // x ∈ Z n} : ℝ) - E.card) ≤
          (SoficGroups.boundary (τ n) E : ℝ))
    (hbad : Tendsto
      (fun n =>
        ((SoficGroups.MatchedComponentCompletion.sourceCompletionBad
          (σ n) (p n) F (Z n)).card : ℝ) / (Z n).card)
      atTop (𝓝 0)) :
    Nonempty (SoficGroups.ExpandingCentralizerFiniteModel J F) := by sorry
