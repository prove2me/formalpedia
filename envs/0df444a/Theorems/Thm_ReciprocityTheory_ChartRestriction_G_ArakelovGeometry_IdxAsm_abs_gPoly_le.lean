-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_IdxAsm_abs_gPoly_le
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm.abs_gPoly_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:11:23.717419+00:00
-- url     : https://prove2.me/theorems/1289465f-c3f1-429c-85ec-5450b3b34544
-- title:
--   Idx Asm: abs g Poly le
-- statement:
--   The Idx Asm construction uses the abs g Poly le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IdxAssembleStA.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/IdxAssembleStA.lean#L11-L35

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IdxAssembleStA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm
open Filter Asymptotics Finset

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.IdxAsm.abs_gPoly_le (D : ℕ) (c : ℕ → ℝ) (a b : ℕ) :
    |gPoly D c a b| ≤ (∑ i ∈ range (D + 1), |c i|) * (((a + b : ℕ) : ℝ) + 1) ^ D := by sorry
