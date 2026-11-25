-- Prove2me | Theorems.Thm_PI_WwInjectiveWork_deX_eq_sum
-- name    : PI.WwInjectiveWork.deX_eq_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:57.418991+00:00
-- url     : https://prove2.me/theorems/7c4d8dd2-b055-5ae9-8188-b24da9613a1f
-- title:
--   Ww Injective Work: de X eq sum
-- statement:
--   The Ww Injective Work construction uses the de X eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L28-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L28-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_GramVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwInjectiveWork
open MvPolynomial PI.WwInjective PI.WwInjective.KM
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)

theorem PI.WwInjectiveWork.deX_eq_sum (hCB : PI.WwCauchyBinet.WwCauchyBinet) {K : Type} [CommRing K]
    (y : Lt → Fin N → ℕ → K) :
    DeX N nu y = ∑ J : ColChoice N nu, C (minY N nu J y) *
      map (Int.castRingHom K) (nablaX N nu J) := by sorry
