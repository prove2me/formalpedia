-- Prove2me | Theorems.Thm_PI_WAU_B_exists_nat_adele
-- name    : PI.WAU.B.exists_nat_adele
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:43:49.022191+00:00
-- url     : https://prove2.me/theorems/e0128b7a-9c04-47e6-afec-1a91ed4db45b
-- title:
--   B: exists nat adele
-- statement:
--   The B construction uses the exists nat adele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L31-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdelicUnimodularity/ExistsNatLocal.lean#L31-L46

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

theorem PI.WAU.B.exists_nat_adele (a : FiniteAdeleRing (𝓞 F) F) :
    ∃ n : ℕ, 0 < n ∧ ∀ v, ((n : FiniteAdeleRing (𝓞 F) F) * a) v ∈ v.adicCompletionIntegers F := by sorry
