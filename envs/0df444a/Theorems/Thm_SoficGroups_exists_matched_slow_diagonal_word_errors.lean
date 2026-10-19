-- Prove2me | Theorems.Thm_SoficGroups_exists_matched_slow_diagonal_word_errors
-- name    : SoficGroups.exists_matched_slow_diagonal_word_errors
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/cb0d004a-41c9-41c3-9e60-c763b526767f
-- title:
--   SoficGroups.exists_matched_slow_diagonal_word_errors
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.exists_matched_slow_diagonal_word_errors
    {V : ℕ → Type*} [∀ n, DecidableEq (V n)] {ι : Type*}
    (U : ∀ n, Finset (V n))
    (P Q : ∀ n, Finpartition (U n))
    (R : ∀ n, Finset (Finset (V n)))
    (hR : ∀ n, R n ⊆ (P n).parts)
    (D : ∀ n, Finset (V n) → Finset (V n))
    (hD : ∀ n C, C ∈ R n → D n C ∈ (Q n).parts)
    (hmajor : ∀ n C, C ∈ R n →
      (D n C).card < 2 * (C ∩ D n C).card)
    (hdiscard : Tendsto
      (fun n => (((U n \ matchedRetainedSupport (R n)).card : ℝ) /
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
          (partitionWordCrossing (Q n) (w n i)).card : ℕ) : ℝ) /
          (U n).card)
      atTop (𝓝 0))
    (B : ∀ n, ℕ → Finset (V n))
    (hbad : ∀ k, Tendsto
      (fun n => (((U n ∩ B n k).card : ℝ) / (U n).card))
      atTop (𝓝 0)) :
    ∃ r : ℕ → ℕ,
      Tendsto r atTop atTop ∧
        Tendsto
          (fun n =>
            (((∑ i ∈ I (r n),
                (partitionWordCrossing (P n) (w n i)).card : ℕ) : ℝ) +
              (U n ∩ B n (r n)).card) / (U n).card)
          atTop (𝓝 0) := by sorry
