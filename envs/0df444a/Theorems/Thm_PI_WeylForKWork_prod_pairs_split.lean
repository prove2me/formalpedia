-- Prove2me | Theorems.Thm_PI_WeylForKWork_prod_pairs_split
-- name    : PI.WeylForKWork.prod_pairs_split
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:39.725952+00:00
-- url     : https://prove2.me/theorems/b55d604a-9765-5521-af88-aae124d1739b
-- title:
--   Weyl For KWork: prod pairs split
-- statement:
--   The Weyl For KWork construction uses the prod pairs split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L150-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L150-L183

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}

theorem PI.WeylForKWork.prod_pairs_split {M : Type*} [CommMonoid M] (ε : Fin N → Bool) (g : Fin N → Fin N → M) :
    ∏ a : Fin N, ∏ b ∈ univ.filter (fun b => a < b ∧ ε a = ε b), g a b =
      (∏ i, ∏ j ∈ univ.filter (fun j => i < j), g (ePl ε i) (ePl ε j)) *
        ∏ i, ∏ j ∈ univ.filter (fun j => i < j), g (eMi ε i) (eMi ε j) := by sorry
