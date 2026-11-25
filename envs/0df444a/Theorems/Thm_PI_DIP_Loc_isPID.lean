-- Prove2me | Theorems.Thm_PI_DIP_Loc_isPID
-- name    : PI.DIP.Loc.isPID
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:14.446058+00:00
-- url     : https://prove2.me/theorems/4102c158-7c70-5595-b341-51eedf082bf5
-- title:
--   Loc: is PID
-- statement:
--   The Loc construction uses the is PID property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/SmulMemOfMemSpan.lean#L102-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/SmulMemOfMemSpan.lean#L102-L112

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantIdentity_SmulMemOfMemSpan
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
open PI PI.DIP PI.DIP.Loc
variable (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime]
variable {K p}
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem PI.DIP.Loc.isPID (K : Type) [Field K] [NumberField K] (p : ℕ) [hp : Fact p.Prime] :
    IsPrincipalIdealRing (A K p) := by sorry
