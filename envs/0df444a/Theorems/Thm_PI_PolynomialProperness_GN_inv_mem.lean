-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_inv_mem
-- name    : PI.PolynomialProperness.GN.inv_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:51:03.686052+00:00
-- url     : https://prove2.me/theorems/193245eb-1201-4b85-a426-dfbb5dc6c2fe
-- title:
--   GN: inv mem
-- statement:
--   The GN construction uses the inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L27-L28

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

theorem PI.PolynomialProperness.GN.inv_mem {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : g⁻¹ ∈ B.GV k r := by sorry
