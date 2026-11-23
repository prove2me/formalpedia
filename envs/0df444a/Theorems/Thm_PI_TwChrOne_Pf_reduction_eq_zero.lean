-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_reduction_eq_zero
-- name    : PI.TwChrOne.Pf.reduction_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:22:02.829829+00:00
-- url     : https://prove2.me/theorems/a541a78f-fac0-4325-9dd3-2fc9c06850f0
-- title:
--   Pf: reduction eq zero
-- statement:
--   The Pf construction uses the reduction eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L48-L51

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

theorem PI.TwChrOne.Pf.reduction_eq_zero {a : E} {p r s : 𝓞 E} (hp : p ∈ P.asIdeal) (hs : s ∉ P.asIdeal)
    (h : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E p * algebraMap (𝓞 E) E r) : redP P a = 0 := by sorry
