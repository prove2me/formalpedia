-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_exists_family_size_of_even
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.exists_family_size_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:35:56.046774+00:00
-- url     : https://prove2.me/theorems/e077742e-1c57-418e-a189-5eadfb0bfffc
-- title:
--   BH12 Even Family: exists family size of even
-- statement:
--   Reindexed acceptance form: an even `k` gets exactly `k+3` rows and `3k+8` columns.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L50-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L50-L55

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.exists_family_size_of_even {k : Nat} (hk : Even k) :
    ∃ q : Nat, k = logicalCount q ∧
      Fintype.card (Sum (OddRow q) EvenRow) = k + 3 ∧
      Fintype.card (Column q) = 3 * k + 8 := by sorry
