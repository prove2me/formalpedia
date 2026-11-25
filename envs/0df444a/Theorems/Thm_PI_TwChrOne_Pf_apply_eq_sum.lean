-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_apply_eq_sum
-- name    : PI.TwChrOne.Pf.apply_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:01.140458+00:00
-- url     : https://prove2.me/theorems/9e91dffd-a2c9-5bc5-9264-f88974287aa0
-- title:
--   Pf: apply eq sum
-- statement:
--   The Pf construction uses the apply eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L146-L152

import Definitions.Def_Formalism_PeriodIntegrals_TwChrOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedCharacterOne_IsIntegralAtSuperdiagonalSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.TwChrOne PI.TwChrOne.Pf
variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
variable {n : ℕ}

theorem PI.TwChrOne.Pf.apply_eq_sum (f : Sp E n ≃ₗ[E] Sp E n) (v : Sp E n) (i : Fin n) :
    f v i = ∑ m, v m * f (Loc.eN E n m.1) i := by sorry
