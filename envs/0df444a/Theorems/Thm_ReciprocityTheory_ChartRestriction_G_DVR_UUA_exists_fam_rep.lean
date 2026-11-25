-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_UUA_exists_fam_rep
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:58.484802+00:00
-- url     : https://prove2.me/theorems/e1df5c83-da15-4dae-810f-a8b455cb5907
-- title:
--   UUA: exists fam rep
-- statement:
--   The UUA construction uses the exists fam rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsFamRep.lean#L49-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ExistsFamRep.lean#L49-L134

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValPowGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_PhiPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.UUA
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem ReciprocityTheory.ChartRestriction.G.DVR.UUA.exists_fam_rep (hG : GlobalFnsSt) (hB : D.TauBimult) (k : ℕ) (ρ : D.X)
    (hcls : ∀ a b : D.X, ρ + k • a = ρ + k • b → a = b)
    (σ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F ρ) (DegPre.famε k))) :
    ∃ s : Fam D F k, s.s ρ = σ ∧ ∀ β : D.X, (∀ mu, ρ + k • mu ≠ β) → ∀ j, (s.s β).f j = 0 := by sorry
