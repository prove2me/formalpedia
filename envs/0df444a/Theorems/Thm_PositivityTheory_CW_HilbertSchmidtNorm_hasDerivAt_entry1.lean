-- Prove2me | Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hasDerivAt_entry1
-- name    : PositivityTheory.CW.HilbertSchmidtNorm.hasDerivAt_entry1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:41.667951+00:00
-- url     : https://prove2.me/theorems/c81a332f-f43b-4e75-ac15-e30bac97b213
-- title:
--   Hilbert Schmidt Norm: has Deriv At entry1
-- statement:
--   The Hilbert Schmidt Norm construction uses the has Deriv At entry1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L58-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L58-L61

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.HilbertSchmidtNorm
variable {n : ℕ}

theorem PositivityTheory.CW.HilbertSchmidtNorm.hasDerivAt_entry1 (g X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X)) i j)
      ((g * NormedSpace.exp (t • X) * X) i j) t := by sorry
