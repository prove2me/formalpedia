-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LocBasisSemi_isPID
-- name    : PI.UnitaryGroupMassFormula.LocBasisSemi.isPID
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:39:52.016432+00:00
-- url     : https://prove2.me/theorems/1fab1a4e-b9ad-4824-9c14-8b4e6da74971
-- title:
--   Loc Basis Semi: is PID
-- statement:
--   The Loc Basis Semi construction uses the is PID property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/IsPID.lean#L11-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemilocalBasis/IsPID.lean#L11-L21

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocBasisSemi
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_SmulMemOfMemSpan
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemilocalBasis_IsPID
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LocBasisSemi

theorem PI.UnitaryGroupMassFormula.LocBasisSemi.isPID (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    IsPrincipalIdealRing (A K p) := by sorry
