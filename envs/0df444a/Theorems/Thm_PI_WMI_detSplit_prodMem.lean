-- Prove2me | Theorems.Thm_PI_WMI_detSplit_prodMem
-- name    : PI.WMI.detSplit_prodMem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:47:48.231385+00:00
-- url     : https://prove2.me/theorems/459da6df-52e7-47bf-8f65-aade5bafa5cd
-- title:
--   WMI: det Split prod Mem
-- statement:
--   The WMI construction uses the det Split prod Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/DetSplit.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/PolynomialModelIsometry/DetSplit.lean#L31-L53

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

theorem PI.WMI.detSplit_prodMem {N K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ N) (I : ∀ k, Fin (sz k) → Fin N)
    (s : Finset (Fin K)) :
    ∏ k ∈ s, initMinor ℂ (I k) (hsz k) ∈
      Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (fun t => (s.filter fun k => t.val < sz k).card) := by sorry
