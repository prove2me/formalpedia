-- Prove2me | Theorems.Thm_SoficGroups_KunCombinedPrescribedRootSourceTolerance_exists_prescribed_radius_union_source_completed_tolerance
-- name    : SoficGroups.KunCombinedPrescribedRootSourceTolerance.exists_prescribed_radius_union_source_completed_tolerance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/f8f27bcf-03b6-42fc-8005-536d2b28a941
-- title:
--   SoficGroups.KunCombinedPrescribedRootSourceTolerance.exists_prescribed_radius_union_source_completed_tolerance
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCombinedPrescribedRootSourceTolerance
open Filter Topology

theorem SoficGroups.KunCombinedPrescribedRootSourceTolerance.exists_prescribed_radius_union_source_completed_tolerance
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (hVpositive : ∀ n, 0 < Fintype.card (V n))
    (hV : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (root : (n : ℕ) → ℕ → Finset (V n))
    (source : (n : ℕ) → Finset (V n))
    (hroot : ∀ r : ℕ,
      Tendsto
        (fun n => ((root n r).card : ℝ) / Fintype.card (V n))
        atTop (𝓝 0))
    (hsource : Tendsto
      (fun n => ((source n).card : ℝ) / Fintype.card (V n))
      atTop (𝓝 0))
    (δ : ℕ → ℝ)
    (hδpositive : ∀ j, 0 < δ j)
    (hδ : Tendsto δ atTop (𝓝 0))
    (R : ℕ → ℕ) (hR : ∀ j, j ≤ R j)
    (d : ℕ) (hd : 0 < d)
    (ell q : ℝ) (hell : 0 < ell) (hq : q < 1) :
    ∃ m rootError t : ℕ → ℕ,
      Tendsto m atTop atTop ∧
      Tendsto (fun n => R (m n)) atTop atTop ∧
      Tendsto (fun n => δ (m n)) atTop (𝓝 0) ∧
      Tendsto
        (fun n =>
          (((root n (R (m n)) ∪ source n).card : ℝ) /
            (δ (m n) * (Fintype.card (V n) : ℝ))))
        atTop (𝓝 0) ∧
      (∀ n,
        rootError n =
          Nat.ceil (δ (m n) * (Fintype.card (V n) : ℝ))) ∧
      (∀ n,
        δ (m n) ≤
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ)) ∧
      Tendsto
        (fun n =>
          (rootError n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        t n =
          2 * d * (root n (R (m n)) ∪ source n).card +
            rootError n + 1) ∧
      (∀ n, 0 < t n) ∧
      (∀ n,
        2 * d * (root n (R (m n))).card ≤ t n) ∧
      (∀ n,
        2 * d * (source n).card ≤ t n) ∧
      (∀ n, rootError n ≤ t n) ∧
      Tendsto
        (fun n =>
          (t n : ℝ) / (Fintype.card (V n) : ℝ))
        atTop (𝓝 0) ∧
      (∀ n,
        ell * δ (m n) / (2 * (ell + 8 * (d : ℝ))) ≤
          ell * (t n : ℝ) /
            (2 * (ell + 8 * (d : ℝ)) *
              (Fintype.card (V n) : ℝ))) ∧
      (∀ᶠ n in atTop,
        (10 : ℝ) * (t n : ℝ) <
          ell * (Fintype.card (V n) : ℝ)) ∧
      (∀ᶠ n in atTop,
        (5 : ℝ) *
            (4 + ell *
              (216 / ((d : ℝ) * (1 - q) ^ 2) +
                1 / (d : ℝ))) * (t n : ℝ) ≤
          ell * (Fintype.card (V n) : ℝ)) := by sorry
