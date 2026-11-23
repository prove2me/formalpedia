-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrWord_mem
-- name    : ReciprocityTheory.ChartRestriction.DS.kirrWord_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:19.917626+00:00
-- url     : https://prove2.me/theorems/9eb8521b-6de8-4cef-aec5-69df63723155
-- title:
--   DS: kirr Word mem
-- statement:
--   The DS construction uses the kirr Word mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L61-L62

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

theorem ReciprocityTheory.ChartRestriction.DS.kirrWord_mem (u : X) {l : List (Fin n × Fin n)} (hl : KirrLow ε l) :
    kirrWord A u l ∈ kirrSpan ε A u := by sorry
