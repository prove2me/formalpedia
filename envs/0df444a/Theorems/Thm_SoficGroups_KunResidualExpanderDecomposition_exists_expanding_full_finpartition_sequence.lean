-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_exists_expanding_full_finpartition_sequence
-- name    : SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/76bed669-10b5-4215-9c10-327fb04ecb10
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunResidualExpanderDecomposition.exists_expanding_full_finpartition_sequence
    (ι : Type*) [Fintype ι]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)]
    [∀ n, Nonempty (V n)]
    [∀ n, DecidableEq (V n)]
    (σ : (n : ℕ) → ι → Equiv.Perm (V n))
    (B : (n : ℕ) → Finset (V n))
    (γ : ℝ) (hγ : 0 < γ)
    (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n)
    (hαzero : Tendsto α atTop (nhds 0))
    (hbad : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0))
    (himprove : ∀ n (T : Finset (V n)),
      T ⊆ Finset.univ \ B n →
      (SoficGroups.boundary (σ n) T : ℝ) <
        γ * (T.card : ℝ) →
      ∃ U : Finset (V n), 3 * (U ∆ T).card < T.card ∧
        (SoficGroups.boundary (σ n) U : ℝ) ≤
          α n * (U.card : ℝ)) :
    ∃ P : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)),
      0 < γ ∧
      (∀ n, ∀ C ∈ (P n).parts, ∀ E : Finset (V n), E ⊆ C →
        2 * E.card ≤ C.card →
          γ * (E.card : ℝ) ≤
            (SoficGroups.boundary (σ n) E : ℝ)) ∧
      Tendsto
        (fun n =>
          (∑ C ∈ (P n).parts,
            (SoficGroups.boundary (σ n) C : ℝ)) /
              Fintype.card (V n))
        atTop (nhds 0) := by sorry
