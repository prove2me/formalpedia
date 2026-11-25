-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_CntFormula_UG_num_mem_both
-- name    : PI.UnitaryGroupMassFormula.CntFormula.UG.num_mem_both
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:45:15.272034+00:00
-- url     : https://prove2.me/theorems/b50887cb-fb64-51cf-b28e-8d8512f39bd9
-- title:
--   UG: num mem both
-- statement:
--   The UG construction uses the num mem both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsTraceNotMem.lean#L35-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CountingFormula/ExistsTraceNotMem.lean#L35-L91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_PairUnitLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountingFormula_ExistsTraceNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.CntFormula PI.UnitaryGroupMassFormula.CntFormula.UG
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem PI.UnitaryGroupMassFormula.CntFormula.UG.num_mem_both {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p) (hst : star a = a)
    (hna : ¬ IsUnitIn (locRing p) a) :
    ∃ a₁ : 𝓞 K, ∃ s₁ ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p,
      a = algebraMap (𝓞 K) K a₁ / algebraMap (𝓞 K) K s₁ ∧ a₁ ∈ p ∧ a₁ ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) p := by sorry
