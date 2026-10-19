-- Prove2me | Theorems.Thm_SoficGroups_SourceCommonComponentComparisonBad_transported_comparisonBad_density_tendsto_zero
-- name    : SoficGroups.SourceCommonComponentComparisonBad.transported_comparisonBad_density_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/0ca51189-1336-4b78-8633-c4c9e0f94dc5
-- title:
--   SoficGroups.SourceCommonComponentComparisonBad.transported_comparisonBad_density_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceCommonComponentComparisonBad.transported_comparisonBad_density_tendsto_zero
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (Q : (n : ℕ) → Finpartition (Finset.univ : Finset (V n)))
    (T : (n : ℕ) → Equiv.Perm (V n))
    (eta : ℕ → ℝ)
    (hoverlap : Tendsto
      (fun n =>
        (∑ C ∈ SoficGroups.insufficientOverlapComponents
          (SoficGroups.transportedUnivFinpartition (Q n) (T n))
          (Q n) (eta n), (C.card : ℝ)) /
            Fintype.card (V n))
      atTop (nhds 0))
    (hloss : Tendsto
      (fun n =>
        (∑ C ∈
          (SoficGroups.transportedUnivFinpartition (Q n) (T n)).parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart (Q n) C).card : ℝ))) /
              Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((comparisonBad (Q n) (T n) (eta n)).card : ℝ) /
          Fintype.card (V n))
      atTop (nhds 0) := by sorry
