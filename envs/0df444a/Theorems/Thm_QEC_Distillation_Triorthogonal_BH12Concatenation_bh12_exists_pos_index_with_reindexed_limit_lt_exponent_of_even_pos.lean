-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:30:28.642045+00:00
-- url     : https://prove2.me/theorems/f90d6a1f-881b-4ceb-9277-66ddc8685c79
-- title:
--   BH12 Concatenation: bh12 exists pos index with reindexed limit lt exponent of even pos
-- statement:
--   Every positive even source count has a positive BH12 index whose exact
--   reindexed exponent remains strictly above the limiting exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L136-L145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L136-L145

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12_exists_pos_index_with_reindexed_limit_lt_exponent_of_even_pos
    {k : Nat} (hk : Even k) (hpos : 0 < k) :
    ∃ q : Nat, 0 < q ∧ k = logicalCount q ∧
      bh12BlockExponent q =
        Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 ∧
      Real.log 3 / Real.log 2 < bh12BlockExponent q := by sorry
