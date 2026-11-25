-- Prove2me | Theorems.Thm_PI_UMultOne_UnitaryGroupMassFormula_emb_continuous
-- name    : PI.UMultOne.UnitaryGroupMassFormula.emb_continuous
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:30:18.100391+00:00
-- url     : https://prove2.me/theorems/2051b97d-84ee-4008-aa30-95bd1861f4cb
-- title:
--   Unitary Group Mass Formula: emb continuous
-- statement:
--   The Unitary Group Mass Formula construction uses the emb continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L46-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitarySecondCountable/Assembly.lean#L46-L58

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UMultOne PI.UMultOne.UnitaryGroupMassFormula
open Matrix Set

theorem PI.UMultOne.UnitaryGroupMassFormula.emb_continuous (n : ℕ) (ι : Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin (n + 1)) ℂ)
    (hι : ∀ g, ((ι g : Matrix.unitaryGroup (Fin (n + 1)) ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))) :
    Continuous ι := by sorry
