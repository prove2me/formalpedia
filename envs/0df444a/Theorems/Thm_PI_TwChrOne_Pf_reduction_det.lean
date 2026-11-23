-- Prove2me | Theorems.Thm_PI_TwChrOne_Pf_reduction_det
-- name    : PI.TwChrOne.Pf.reduction_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:41:59.061849+00:00
-- url     : https://prove2.me/theorems/69858cc1-c8ac-4bb6-88d9-5616faa0d039
-- title:
--   Pf: reduction det
-- statement:
--   The Pf construction uses the reduction det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L114-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TwistedCharacterOne/IsIntegralAtSuperdiagonalSum.lean#L114-L120

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

theorem PI.TwChrOne.Pf.reduction_det {m : ℕ} (M : Matrix (Fin m) (Fin m) E) (hM : ∀ s t, IntAt P (M s t)) :
    redP P M.det = (M.map (redP P)).det := by sorry
