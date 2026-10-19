-- Prove2me | Theorems.Thm_SoficGroups_KunResidualRetainedSelection_exists_matched_slow_diagonal_large_components_on_source_scale_tail
-- name    : SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_source_scale_tail
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/330088a8-93c6-49b8-bb8d-75644adcfd6c
-- title:
--   SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_source_scale_tail
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

theorem SoficGroups.KunResidualRetainedSelection.exists_matched_slow_diagonal_large_components_on_source_scale_tail
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
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0))
    (hmajor : ∀ n,
      eta n ≤ (1 : ℝ) / 2 →
      2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 →
        ∀ C, C ∈ R n →
          (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n =>
        (((U n \ SoficGroups.matchedRetainedSupport (R n)).card : ℝ) /
          (U n).card)) atTop (𝓝 0))
    (hsymm : Tendsto
      (fun n =>
        ((∑ C ∈ R n, (C ∆ D n C).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (I : ℕ → Finset ι)
    (w : ∀ n, ι → Equiv.Perm (V n))
    (hword : ∀ k, Tendsto
      (fun n =>
        ((∑ i ∈ I k,
          (SoficGroups.partitionWordCrossing (Q n) (w n i)).card :
            ℕ) : ℝ) / (U n).card)
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
            Set.MapsTo f (↑(S ^ (k / 2)) : Set K)
              (↑C : Set (V n)) ∧
              Set.InjOn f (↑(S ^ (k / 2)) : Set K))
    (N₀ : ℕ) :
    ∃ (N : ℕ) (r : ℕ → ℕ)
      (C : (n : ℕ) → Finset (V (n + N))),
      N₀ ≤ N ∧
        (∀ n, eta (n + N) ≤ (1 : ℝ) / 2) ∧
        (∀ n,
          2 * (Real.exp (H (n + N)) - 1 +
            2 * eta (n + N)) < 1) ∧
        Tendsto r atTop atTop ∧
        (∀ n, C n ∈ R (n + N)) ∧
        Tendsto
          (fun n =>
            (SoficGroups.boundary (σ (n + N)) (C n) : ℝ) /
              (C n).card)
          atTop (𝓝 0) ∧
        Tendsto
          (fun n =>
            (((C n ∩
              SoficGroups.matchedRadiusBad
                (P (n + N)) (I (r n)) (w (n + N))
                (B (n + N) (r n))).card : ℝ) /
                  (C n).card))
          atTop (𝓝 0) ∧
        Tendsto (fun n => (C n).card) atTop atTop := by sorry
