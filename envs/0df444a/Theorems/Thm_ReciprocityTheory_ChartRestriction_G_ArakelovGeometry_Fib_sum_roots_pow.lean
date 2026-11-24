-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_sum_roots_pow
-- name    : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.sum_roots_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:19.547943+00:00
-- url     : https://prove2.me/theorems/94fc138f-e040-47ae-8ee7-c7b1f8b786e5
-- title:
--   Fib: sum roots pow
-- statement:
--   The Fib construction uses the sum roots pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStC.lean#L57-L65

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib.sum_roots_pow {K : Type*} [Field K] (p : Polynomial K) (hm : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) (k : ℕ) :
    (p.roots.map (· ^ k)).sum = psumC p p.natDegree k := by sorry
