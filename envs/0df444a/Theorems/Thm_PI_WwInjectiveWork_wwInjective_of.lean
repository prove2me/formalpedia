-- Prove2me | Theorems.Thm_PI_WwInjectiveWork_wwInjective_of
-- name    : PI.WwInjectiveWork.wwInjective_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:02.721912+00:00
-- url     : https://prove2.me/theorems/5dfc6ae9-5b8f-4104-8768-85ab607db1db
-- title:
--   Ww Injective Work: ww Injective of
-- statement:
--   The Ww Injective Work construction uses the ww Injective of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GramInjectivity/InstFintypeColChoice.lean#L55-L58

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

theorem PI.WwInjectiveWork.wwInjective_of (hCB : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by sorry
