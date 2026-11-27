-- Prove2me | Theorems.Thm_PI_PolynomialProperness_GN_gN_le_of_entry
-- name    : PI.PolynomialProperness.GN.gN_le_of_entry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:38.189815+00:00
-- url     : https://prove2.me/theorems/1e054b5c-ee7f-4498-a0cd-265bde3c5a20
-- title:
--   GN: g N le of entry
-- statement:
--   The GN construction uses the g N le of entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L164-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialProperness/ZhatNormLinearBound.lean#L164-L172

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

theorem PI.PolynomialProperness.GN.gN_le_of_entry {k r : ℕ} (g : B.Mat k r) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖g i j‖ ≤ c) :
    B.gN g ≤ (2 * r + k + 1 : ℕ) * c := by sorry
