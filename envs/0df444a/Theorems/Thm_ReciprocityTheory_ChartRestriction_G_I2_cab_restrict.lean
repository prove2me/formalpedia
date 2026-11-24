-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cab_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cab_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:42.578622+00:00
-- url     : https://prove2.me/theorems/8181e04b-e53e-45f9-9f18-700aa78a10db
-- title:
--   I2: cab restrict
-- statement:
--   The I2 construction uses the cab restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L140-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/ColAbelA.lean#L140-L150

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContDiffOfDifferentiableFd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ColAbelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section

theorem ReciprocityTheory.ChartRestriction.G.I2.cab_restrict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Sb : Submodule ℂ V)
    {c : ℕ} {f g : V → ℂ} (hf : ContDiff ℂ c f) (hg : ContDiff ℂ c g) (hfg : ∀ v ∈ Sb, f v = g v)
    (x : Fin c → V) (hx : ∀ k, x k ∈ Sb) :
    iteratedFDeriv ℂ c f 0 x = iteratedFDeriv ℂ c g 0 x := by sorry
