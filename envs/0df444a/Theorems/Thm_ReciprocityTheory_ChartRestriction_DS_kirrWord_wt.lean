-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirrWord_wt
-- name    : ReciprocityTheory.ChartRestriction.DS.kirrWord_wt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:52:05.910167+00:00
-- url     : https://prove2.me/theorems/fc603dc8-4606-4488-b6ab-4c80fb1610eb
-- title:
--   DS: kirr Word wt
-- statement:
--   The DS construction uses the kirr Word wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L44-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L44-L59

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

theorem ReciprocityTheory.ChartRestriction.DS.kirrWord_wt (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : ∀ a, A a a u = (ν a : ℂ) • u) :
    ∀ l a, A a a (kirrWord A u l) = (kirrWt ν l a : ℂ) • kirrWord A u l
  := by sorry
