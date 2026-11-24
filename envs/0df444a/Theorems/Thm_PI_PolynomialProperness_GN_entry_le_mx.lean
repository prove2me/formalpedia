-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_entry_le_mx
-- name    : PI.PolynomialProperness.GN.entry_le_mx
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:51:07.153488+00:00
-- url     : https://prove2.me/theorems/92e59a3c-b528-47be-8957-71b6411b4ce4
-- title:
--   GN: entry le mx
-- statement:
--   The GN construction uses the entry le mx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L176-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L176-L180

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialProperness_ZhatNormLinearBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.PolynomialProperness PI.PolynomialProperness.GN
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt

theorem PI.PolynomialProperness.GN.entry_le_mx {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : ‖M i j‖ ≤ C2.mx M := by sorry
