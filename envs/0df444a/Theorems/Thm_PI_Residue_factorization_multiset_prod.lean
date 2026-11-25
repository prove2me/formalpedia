-- Prove2me | Theorems.Thm_PI_Residue_factorization_multiset_prod
-- name    : PI.Residue.factorization_multiset_prod
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:51.244792+00:00
-- url     : https://prove2.me/theorems/c16e29ca-0798-4203-b95b-5474b9ffa666
-- title:
--   Residue: factorization multiset prod
-- statement:
--   The Residue construction uses the factorization multiset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/FactorizationMultisetProd.lean#L30-L41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open scoped ENNReal
variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

theorem PI.Residue.factorization_multiset_prod (m : Multiset ℕ) (h : ∀ x ∈ m, x ≠ 0) (p : ℕ) :
    m.prod.factorization p = (m.map (fun x => x.factorization p)).sum := by sorry
