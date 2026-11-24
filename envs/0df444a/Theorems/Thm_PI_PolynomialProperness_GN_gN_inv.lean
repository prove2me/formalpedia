-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_gN_inv
-- name    : PI.PolynomialProperness.GN.gN_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:54:20.768543+00:00
-- url     : https://prove2.me/theorems/4fff687b-9eb0-432b-b04d-aabb6d4943fd
-- title:
--   GN: g N inv
-- statement:
--   The GN construction uses the g N inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L94-L95

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

theorem PI.PolynomialProperness.GN.gN_inv {k r : ℕ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : B.gN g⁻¹ = B.gN g := by sorry
