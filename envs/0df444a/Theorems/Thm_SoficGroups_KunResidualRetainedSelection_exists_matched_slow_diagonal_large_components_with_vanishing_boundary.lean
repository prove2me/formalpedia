-- Prove2me | Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matched_slow_diagonal_large_components_with_vanishing_boundary
-- name    : SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_with_vanishing_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/57d98075-f202-4eff-a7e3-899b43666acf
-- title:
--   SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_with_vanishing_boundary
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff

theorem SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_with_vanishing_boundary
    {K : Type*} [Group K] [Infinite K] [DecidableEq K]
    (S : Finset K) (hS : 1 ∈ S)
    (hgen : Subgroup.closure (S : Set K) = ⊤)
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)]
    {ι κ : Type*} [Fintype κ]
    (σ : (n : ℕ) → κ → Equiv.Perm (V n))
    (U : ∀ n, Finset (V n)) (hU : ∀ n, (U n).Nonempty)
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (hRne : ∀ n, (R n).Nonempty)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) / (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (SoficGroups.partitionWordCrossing (Q n) (w n i)).card : ℕ) :
            ℝ) / (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0))
    (hboundary : Tendsto
      (fun n =>
        (∑ C ∈ (P n).parts, (SoficGroups.boundary (σ n) C : ℝ)) /
          (U n).card) atTop (𝓝 0))
    (hrealize : ∀ n k (C : Finset (V n)), C ∈ R n →
      ∀ x ∈ C,
        x ∉ SoficGroups.matchedRadiusBad
          (P n) (I k) (w n) (B n k) →
          ∃ f : K → V n,
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K) (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K)) :
    ∃ (r : ℕ → ℕ) (C : ∀ n, Finset (V n)),
      Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R n) ∧
        Tendsto
          (fun n =>
            (SoficGroups.boundary (σ n) (C n) : ℝ) / (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              SoficGroups.matchedRadiusBad
                (P n) (I (r n)) (w n) (B n (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by sorry
