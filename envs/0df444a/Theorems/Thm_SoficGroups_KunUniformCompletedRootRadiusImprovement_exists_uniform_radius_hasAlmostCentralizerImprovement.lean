-- Prove2me | Theorems.Thm_SoficGroups_KunUniformCompletedRootRadiusImprovement_exists_uniform_radius_hasAlmostCentralizerImprovement
-- name    : SoficGroups.KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/12491aa2-3688-4bb8-8923-9aba30238ebb
-- title:
--   SoficGroups.KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniformCompletedRootRadiusImprovement
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u

theorem SoficGroups.KunUniformCompletedRootRadiusImprovement.exists_uniform_radius_hasAlmostCentralizerImprovement
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, u} G)
    (S : Finset G) (honeS : 1 ∈ S)
    (hcover : P.generators ⊆ S)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (w : G → List ↥S)
    (h α : ℝ) (hpositive : 0 < h) (hα : 0 < α) :
    ∃ r : ℕ,
      ∀ (V : Type u) [Fintype V] [Nonempty V] [DecidableEq V]
        (σ : ↥S → Equiv.Perm V) (φ : G → Equiv.Perm V)
        (tolerance : ℕ) (B : Finset V),
      (∀ g : G, φ g = ((w g).map σ).prod) →
      φ 1 = 1 →
      (∀ i : ↥S, φ (i : G) = σ i) →
      (∀ A : Finset V,
        h * min (A.card : ℝ)
          ((Fintype.card V : ℝ) - A.card) ≤
            (SoficGroups.boundary σ A : ℝ)) →
      (5 * (4 + h *
        (216 / ((S.card : ℝ) *
          (1 - kazhdanMarkovContractionFactor P S) ^ 2) +
            1 / (S.card : ℝ))) * (tolerance : ℝ) ≤
              h * (Fintype.card V : ℝ)) →
      (tolerance = 0 ∨
        (0 < (tolerance : ℝ) ∧
          α ≤ h * (tolerance : ℝ) /
            (2 * (h + 8 * (S.card : ℝ)) *
              (Fintype.card V : ℝ)) ∧
          2 * (S.card : ℝ) * (B.card : ℝ) ≤
            (tolerance : ℝ) ∧
          ∀ a g : G,
            (w a).length + (w g).length +
                (w (a * g)).length ≤ r →
              ∀ x : V, x ∉ B →
                φ (a * g) x = (φ a * φ g) x)) →
      SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by sorry
