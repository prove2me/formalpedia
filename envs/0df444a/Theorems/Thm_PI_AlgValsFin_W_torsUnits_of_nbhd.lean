-- Prove2me | Theorems.Thm_PI_AlgValsFin_W_torsUnits_of_nbhd
-- name    : PI.AlgValsFin.W.torsUnits_of_nbhd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:24:02.303262+00:00
-- url     : https://prove2.me/theorems/4a9cc6b4-71d1-474e-9473-d914796aaf43
-- title:
--   W: tors Units of nbhd
-- statement:
--   The W construction uses the tors Units of nbhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/TorsUnitsOfNbhd.lean#L52-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/TorsUnitsOfNbhd.lean#L52-L81

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

theorem PI.AlgValsFin.W.torsUnits_of_nbhd (L : Type) [Field L] [NumberField L]
    (hnb : ∀ W : Set (Ideles L), IsOpen W → (1 : Ideles L) ∈ W →
      ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (n : ℕ), ∀ x ∈ UFin L,
        (∀ v ∈ S, Valued.v ((x : AdeleRing (𝓞 L) L).2 v - 1) ≤ WithZero.exp (-(n : ℤ))) → x ∈ W) :
    TorsUnits L := by sorry
