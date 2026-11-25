-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_ntd_pow
-- name    : ReciprocityTheory.ChartRestriction.G.T0.MHF.ntd_pow
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:36:45.746362+00:00
-- url     : https://prove2.me/theorems/99ebd880-d6d2-54fd-a039-034f402d0837
-- title:
--   MHF: ntd pow
-- statement:
--   The MHF construction uses the ntd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/CoeffPsiBNeZero.lean#L59-L64

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.MHF
open MvPolynomial ReciprocityTheory.MultiplicativeHeights
variable {K : Type*} [Field K] {B n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.MHF.ntd_pow {R : Type*} [CommRing R] [IsDomain R] (p : Polynomial R) (hp : p ≠ 0) (m : ℕ) :
    (p ^ m).natTrailingDegree = m * p.natTrailingDegree := by sorry
