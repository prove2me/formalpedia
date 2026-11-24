-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_sub_add_sub_eq
-- name    : ReciprocityTheory.ChartRestriction.DS.ite_sub_add_sub_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:55.381632+00:00
-- url     : https://prove2.me/theorems/75fb9c12-b0b9-4e3c-b605-bd3c83d35c09
-- title:
--   DS: ite sub add sub eq
-- statement:
--   The DS construction uses the ite sub add sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L23-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.ite_sub_add_sub_eq {R : Type*} [AddCommGroup R] (p : Prop) [Decidable p] (A B C D : R) :
    (if p then (A - B) + (C - D) else 0) =
      ((if p then A else 0) - (if p then B else 0)) + ((if p then C else 0) - (if p then D else 0)) := by sorry
