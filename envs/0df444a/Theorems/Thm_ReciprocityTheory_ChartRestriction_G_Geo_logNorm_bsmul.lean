-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_logNorm_bsmul
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.logNorm_bsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:17.097387+00:00
-- url     : https://prove2.me/theorems/75905317-c7b5-4e1c-becc-0f6e38f11667
-- title:
--   Geo: log Norm bsmul
-- statement:
--   The Geo construction uses the log Norm bsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterSheetA.lean#L32-L42

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial Filter Topology
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem ReciprocityTheory.ChartRestriction.G.Geo.logNorm_bsmul (A : HermLine ι) {s : MRing ι} {a : K → ℕ} (hA : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    logNorm A s (bsmul c z) = logNorm A s z := by sorry
