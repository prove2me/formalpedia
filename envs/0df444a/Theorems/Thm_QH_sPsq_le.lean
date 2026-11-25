-- Prove2me | Theorems.Thm_QH_sPsq_le
-- name    : QH.sPsq_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:05.703047+00:00
-- url     : https://prove2.me/theorems/09327d98-9bfb-4fee-8513-073b2e1dccff
-- title:
--   QH: s Psq le
-- statement:
--   The QH construction uses the s Psq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SPsqLe.lean#L161-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/MeanSquareBounds/SPsqLe.lean#L161-L171

import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_PrimeSetTwoBounds
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagB
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SumMinLeDiv
import Definitions.Def_Development_AutomorphicArithmetic_MeanSquareBounds_SPsqLe
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

theorem QH.sPsq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N : ℕ,
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, sP (cN y) N p ^ 2 ≤ C * y * Real.log y := by sorry
