-- Prove2me | Theorems.Thm_PI_DIP_Loc_surjK
-- name    : PI.DIP.Loc.surjK
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:15.505674+00:00
-- url     : https://prove2.me/theorems/e1e94195-cbc0-5c4f-8aeb-9c9adeabe16c
-- title:
--   Loc: surj K
-- statement:
--   The Loc construction uses the surj K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/SmulMemOfMemSpan.lean#L39-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantIdentity/SmulMemOfMemSpan.lean#L39-L48

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

theorem PI.DIP.Loc.surjK (a : A K p) : ∃ s : ℕ, Nat.Coprime s p ∧ ∃ x : 𝓞 K, (s : K) * (a : K) = (x : K) := by sorry
