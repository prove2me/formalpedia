-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_AbelianSchemeGerms_isAbelianScheme_tensor
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:13.896925+00:00
-- url     : https://prove2.me/theorems/388399a5-bfcc-464c-b6eb-ca633b77ccb5
-- title:
--   Abelian Scheme Germs: is Abelian Scheme tensor
-- statement:
--   The Abelian Scheme Germs construction uses the is Abelian Scheme tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AbelianSchemeGerms.lean#L22-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/AbelianSchemeGerms.lean#L22-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegProd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {S : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor (G H : Over S) [GrpObj G] [GrpObj H] (hG : IsAbelianScheme G)
    (hH : IsAbelianScheme H) : IsAbelianScheme (G ⊗ H) := by sorry
