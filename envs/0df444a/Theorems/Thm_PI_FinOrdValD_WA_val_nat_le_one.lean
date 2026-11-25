-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_val_nat_le_one
-- name    : PI.FinOrdValD.WA.val_nat_le_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:40.735372+00:00
-- url     : https://prove2.me/theorems/0781d4ad-2e41-41db-9bff-32195a31f47d
-- title:
--   WA: val nat le one
-- statement:
--   The WA construction uses the val nat le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L24-L26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]

theorem PI.FinOrdValD.WA.val_nat_le_one (v : HeightOneSpectrum (𝓞 L)) (m : ℕ) : v.valuation L (m : L) ≤ 1 := by sorry
