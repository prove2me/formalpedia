-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_scale_multiHomogeneous
-- name    : ReciprocityTheory.ChartRestriction.G.T0.scale_multiHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:56.316451+00:00
-- url     : https://prove2.me/theorems/0727f832-165f-4eb7-b9d9-aa0577fc1c2c
-- title:
--   T0: scale multi Homogeneous
-- statement:
--   The T0 construction uses the scale multi Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L66-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ScaleMultiHomogeneous.lean#L66-L82

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ScaleMultiHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.T0.scale_multiHomogeneous (b : Fin (D + 1)) (u : Kˣ) (a : Fin (D + 1) → ℕ)
    (F : MvPolynomial (TVar D N) K) (hF : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous a F) :
    scaleEquiv (fun v : TVar D N => v.1 = b) u F = C ((u : K) ^ a b) * F := by sorry
