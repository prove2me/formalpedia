-- Prove2me | Theorems.Thm_PI_BlockRatReal_detShift_eq
-- name    : PI.BlockRatReal.detShift_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:32.3348+00:00
-- url     : https://prove2.me/theorems/6b1bec37-4704-42ee-b16d-e3910a48e849
-- title:
--   Block Rat Real: det Shift eq
-- statement:
--   The Block Rat Real construction uses the det Shift eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/AntitoneStar.lean#L14-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/RationalRealBlocks/AntitoneStar.lean#L14-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_EvenStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RationalRealBlocks_AntitoneStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.BlockRatReal

theorem PI.BlockRatReal.detShift_eq {m : ℕ} (w : Fin (m + 1) → ℤ) : detShift w = w (Fin.last m) := by sorry
