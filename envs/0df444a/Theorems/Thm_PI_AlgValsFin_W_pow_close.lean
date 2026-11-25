-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_pow_close
-- name    : PI.AlgValsFin.W.pow_close
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:23:28.5118+00:00
-- url     : https://prove2.me/theorems/24773b85-dd07-582a-872b-953c2acd36b6
-- title:
--   W: pow close
-- statement:
--   The W construction uses the pow close property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/TorsUnitsOfNbhd.lean#L33-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/TorsUnitsOfNbhd.lean#L33-L50

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_EvFLocalIdeleSelf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_NormEqOneOfForallZpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_PowCardSubOneMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_TorsUnitsOfNbhd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open PI PI.AlgValsFin PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]

theorem PI.AlgValsFin.W.pow_close (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ y ∈ UFin L, ∀ v ∈ S,
      Valued.v (((y ^ M : Ideles L) : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ)) := by sorry
