-- Prove2me | Theorems.Thm_QH_exists_primePowerSum_le_mul_log
-- name    : QH.exists_primePowerSum_le_mul_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:20.990137+00:00
-- url     : https://prove2.me/theorems/a311aab5-ae89-4b41-958e-eaa52e742091
-- title:
--   QH: exists prime Power Sum le mul log
-- statement:
--   The QH construction uses the exists prime Power Sum le mul log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SumMinLeDiv.lean#L71-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SumMinLeDiv.lean#L71-L101

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SumMinLeDiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open QH

theorem QH.exists_primePowerSum_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N p : ℕ, sP (cN y) N p ≤ C * Real.log y := by sorry
