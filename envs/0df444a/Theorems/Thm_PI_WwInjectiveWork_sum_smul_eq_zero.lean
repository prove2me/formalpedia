-- Prove2me | Theorems.Thm_PI_WwInjectiveWork_sum_smul_eq_zero
-- name    : PI.WwInjectiveWork.sum_smul_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:18.982546+00:00
-- url     : https://prove2.me/theorems/d3ae9f58-fd11-49e4-af23-ec27b165576f
-- title:
--   Ww Injective Work: sum smul eq zero
-- statement:
--   The Ww Injective Work construction uses the sum smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L39-L53

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

theorem PI.WwInjectiveWork.sum_smul_eq_zero (hCB : PI.WwCauchyBinet.WwCauchyBinet) (l : ℕ) [Fact l.Prime]
    (ph : Module.Dual ℂ_[l] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[l]))
    (hph : ∀ y, ph (DeX N nu y) = 0) :
    ∑ J : ColChoice N nu, ph (map (Int.castRingHom ℂ_[l]) (nablaX N nu J)) •
      map (Int.castRingHom ℂ_[l]) (nablaX N nu J) = 0 := by sorry
