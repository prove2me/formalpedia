-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_val_alg
-- name    : PI.FinOrdValD.WA.val_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:36.497816+00:00
-- url     : https://prove2.me/theorems/fcfe8d70-a9b9-4ff1-a84d-8cb123c6833d
-- title:
--   WA: val alg
-- statement:
--   The WA construction uses the val alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L11-L16

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

theorem PI.FinOrdValD.WA.val_alg (v : HeightOneSpectrum (𝓞 L)) (a : L) :
    Valued.v (algebraMap L (v.adicCompletion L) a) = v.valuation L a := by sorry
