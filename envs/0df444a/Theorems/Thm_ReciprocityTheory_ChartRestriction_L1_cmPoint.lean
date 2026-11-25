-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_cmPoint
-- name    : ReciprocityTheory.ChartRestriction.L1.cmPoint
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:38:07.478867+00:00
-- url     : https://prove2.me/theorems/35f05f63-a82b-4fbb-ad5f-b3d6c0157d4c
-- title:
--   L1: cm Point
-- statement:
--   The L1 construction uses the cm Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModCMPoint.lean#L40-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/UnramifiedIntegrals/ModCMPoint.lean#L40-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModCMPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1

theorem ReciprocityTheory.ChartRestriction.L1.cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by sorry
