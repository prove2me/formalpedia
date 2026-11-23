-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_wa_valued_algebraMap
-- name    : PI.UnitaryApproxFinWork.wa_valued_algebraMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:43:10.973802+00:00
-- url     : https://prove2.me/theorems/908d0cb1-3aab-4fd0-b907-af70080819ff
-- title:
--   Unitary Approx Fin Work: wa valued algebra Map
-- statement:
--   The Unitary Approx Fin Work construction uses the wa valued algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L32-L37

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryApproxFinWork.wa_valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (v.adicCompletion F) k) = v.valuation F k := by sorry
