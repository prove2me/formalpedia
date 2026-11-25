-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_DSIC_mem_UJset_iff
-- name    : PI.UnitaryGroupMassFormula.DSIC.mem_UJset_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:53.064368+00:00
-- url     : https://prove2.me/theorems/dd9274d2-eb04-4ce2-8089-d57410a8e58b
-- title:
--   DSIC: mem UJset iff
-- statement:
--   The DSIC construction uses the mem UJset iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/AdjointEquivalence.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CentralCharacters/AdjointEquivalence.lean#L26-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_QdetMemAdjSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CentralCharacters_AdjointEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DSIC
open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

theorem PI.UnitaryGroupMassFormula.DSIC.mem_UJset_iff {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ PI.UpqRep.UJset ε ↔ gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := by sorry
