-- Prove2me | Theorems.Thm_PI_WAU_B_exists_nat_local
-- name    : PI.WAU.B.exists_nat_local
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:50.411792+00:00
-- url     : https://prove2.me/theorems/8fcf436b-8f90-456b-9f5e-ec2d1d617abc
-- title:
--   B: exists nat local
-- statement:
--   The B construction uses the exists nat local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L14-L29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_ExistsNatLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WAU PI.WAU.B
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
variable {F : Type} [Field F] [NumberField F]

theorem PI.WAU.B.exists_nat_local (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion F) * x ∈ v.adicCompletionIntegers F := by sorry
