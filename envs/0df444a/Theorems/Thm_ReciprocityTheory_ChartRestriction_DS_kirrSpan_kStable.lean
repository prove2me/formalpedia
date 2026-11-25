-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrSpan_kStable
-- name    : ReciprocityTheory.ChartRestriction.DS.kirrSpan_kStable
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:53:30.68268+00:00
-- url     : https://prove2.me/theorems/9cc021ad-f1a8-4999-92d2-2d11915e2428
-- title:
--   DS: kirr Span k Stable
-- statement:
--   The DS construction uses the kirr Span k Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L106-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L106-L112

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.kirrSpan_kStable (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    IsKStableSub ε A (kirrSpan ε A u) := by sorry
