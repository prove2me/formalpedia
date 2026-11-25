-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_hDA_of
-- name    : PI.TwChrOne.Pf.hDA_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:37:32.17277+00:00
-- url     : https://prove2.me/theorems/009425cf-e338-40ad-9e57-867be0421a2c
-- title:
--   Pf: h DA of
-- statement:
--   The Pf construction uses the h DA of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L252-L255

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
variable {kj N c : ℕ}

theorem PI.TwChrOne.Pf.hDA_of {r : Sp E (N + c) ≃ₗ[E] Sp E (N + c)} (hr : r ∈ LocE.JQ P (Ideal.absNorm P.asIdeal) kj N c) :
    ∀ i : Fin (N + c), kj ≤ i.1 → i.1 < N → ∀ j : Fin (N + c), ¬(kj ≤ j.1 ∧ j.1 < N) →
      redP P (r (Loc.eN E (N + c) j.1) i) = 0 := by sorry
