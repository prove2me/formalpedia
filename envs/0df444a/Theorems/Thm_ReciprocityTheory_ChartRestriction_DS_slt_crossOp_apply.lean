-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_slt_crossOp_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.slt_crossOp_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:59:54.760803+00:00
-- url     : https://prove2.me/theorems/84536349-c2c0-5101-8691-7b7220acf8c6
-- title:
--   DS: slt cross Op apply
-- statement:
--   The DS construction uses the slt cross Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/SltEqZeroOfCompact.lean#L75-L84

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NcVOneDecomp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SltEqZeroOfCompact
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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M}

theorem ReciprocityTheory.ChartRestriction.DS.slt_crossOp_apply (k : ℕ) (i : Fin k) (F : Big n k M) (κ : Fin k → Fin n × Fin n) :
    crossOp ε E k i F κ = ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
      ((if (κ i).1 = a then E b a (F (Function.update κ i (b, (κ i).2))) else 0) -
        (if (κ i).2 = b then E b a (F (Function.update κ i ((κ i).1, a))) else 0)) := by sorry
