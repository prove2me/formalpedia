-- Prove2me | Theorems.Thm_PI_WMI_detSplit_fullMinor
-- name    : PI.WMI.detSplit_fullMinor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:01:46.782286+00:00
-- url     : https://prove2.me/theorems/af62636e-a230-5d38-bda4-8ee95f167f7c
-- title:
--   WMI: det Split full Minor
-- statement:
--   The WMI construction uses the det Split full Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/DetSplit.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/DetSplit.lean#L10-L29

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_IsPolyMon
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WMI
open PI.UpqRep Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial Matrix
open scoped InnerProductSpace

theorem PI.WMI.detSplit_fullMinor {N : ℕ} (s : ℕ) (I : Fin s → Fin N) (hs : s ≤ N) (hN : s = N) :
    ∃ e : ℂ, initMinor ℂ (n := N) I hs = C e * detPoly N := by sorry
