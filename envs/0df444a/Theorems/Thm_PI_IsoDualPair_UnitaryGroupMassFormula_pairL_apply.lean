-- Prove2me | Theorems.Thm_PI_IsoDualPair_UnitaryGroupMassFormula_pairL_apply
-- name    : PI.IsoDualPair.UnitaryGroupMassFormula.pairL_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:09:59.809861+00:00
-- url     : https://prove2.me/theorems/4d27bb74-81d9-41fa-a587-ca0eb661edeb
-- title:
--   Unitary Group Mass Formula: pair L apply
-- statement:
--   The Unitary Group Mass Formula construction uses the pair L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDualPair/SymmetricMeasureL2NormEqResolutionL2.lean#L96-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IsometryDualPair/SymmetricMeasureL2NormEqResolutionL2.lean#L96-L96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoDualPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IsometryDualPair_SymmetricMeasureL2NormEqResolutionL2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.IsoDualPair PI.IsoDualPair.UnitaryGroupMassFormula
open PI.IsoDualPair
variable {Lt : Type} [Fintype Lt] {N : ℕ} {nu : Lt → YoungDiagram}

theorem PI.IsoDualPair.UnitaryGroupMassFormula.pairL_apply (φ ψ : Vnu N nu) : pairL φ ψ = prC (φ : LaC N nu) ψ := by sorry
