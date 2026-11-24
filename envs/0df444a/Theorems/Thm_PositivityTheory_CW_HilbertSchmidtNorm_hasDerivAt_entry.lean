-- Prove2me | Theorems.Thm_PositivityTheory_CW_HilbertSchmidtNorm_hasDerivAt_entry
-- name    : PositivityTheory.CW.HilbertSchmidtNorm.hasDerivAt_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:45.452801+00:00
-- url     : https://prove2.me/theorems/0c78275d-19a4-468f-9d72-22a3e8bfc9f3
-- title:
--   Hilbert Schmidt Norm: has Deriv At entry
-- statement:
--   The Hilbert Schmidt Norm construction uses the has Deriv At entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/SecondDerivativeHolds.lean#L14-L27

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
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem PositivityTheory.CW.HilbertSchmidtNorm.hasDerivAt_entry (g X Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => (g * NormedSpace.exp (s • X) * Y) i j)
      ((g * NormedSpace.exp (t • X) * X * Y) i j) t := by sorry
