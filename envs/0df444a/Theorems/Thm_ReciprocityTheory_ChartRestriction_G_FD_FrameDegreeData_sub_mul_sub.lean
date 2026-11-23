-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_sub_mul_sub
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sub_mul_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:04.025138+00:00
-- url     : https://prove2.me/theorems/62c80f49-31d7-4b4e-8625-86ae17501721
-- title:
--   Frame Degree Data: sub mul sub
-- statement:
--   The Frame Degree Data construction uses the sub mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DetSubUpper.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DetSubUpper.lean#L14-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sub_mul_sub {i : ℕ} (h : i ≤ n) (M N : Matrix (Fin n) (Fin n) ℂ)
    (hz : ∀ (a c : Fin i) (k : Fin n), i ≤ (k : ℕ) → M (Fin.castLE h a) k * N k (Fin.castLE h c) = 0) :
    (M * N).submatrix (Fin.castLE h) (Fin.castLE h) =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by sorry
