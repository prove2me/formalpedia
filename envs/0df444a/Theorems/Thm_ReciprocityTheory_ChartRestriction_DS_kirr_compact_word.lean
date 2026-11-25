-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kirr_compact_word
-- name    : ReciprocityTheory.ChartRestriction.DS.kirr_compact_word
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:53:52.669624+00:00
-- url     : https://prove2.me/theorems/93ce0dbb-3586-51ee-93ff-3fe09fc972ff
-- title:
--   DS: kirr compact word
-- statement:
--   The DS construction uses the kirr compact word property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L74-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L74-L104

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

theorem ReciprocityTheory.ChartRestriction.DS.kirr_compact_word (hA : IsGlRep A) {ν : Fin n → ℝ} {u : X} (hu : IsKHWVec ε A ν u) :
    ∀ l, KirrLow ε l → ∀ a b, ε a = ε b → A a b (kirrWord A u l) ∈ kirrSpan ε A u := by sorry
