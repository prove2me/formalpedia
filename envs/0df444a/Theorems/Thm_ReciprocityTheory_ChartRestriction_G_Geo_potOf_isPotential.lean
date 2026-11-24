-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_potOf_isPotential
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.potOf_isPotential
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:11.476931+00:00
-- url     : https://prove2.me/theorems/431e5ccb-92ee-4f95-8806-1a6f299bc103
-- title:
--   Geo: pot Of is Potential
-- statement:
--   The Geo construction uses the pot Of is Potential property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeA.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeA.lean#L81-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeJ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeO
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeQ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeA
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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.Geo.potOf_isPotential (R : AnLogRes P J e) (L : HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) := by sorry
