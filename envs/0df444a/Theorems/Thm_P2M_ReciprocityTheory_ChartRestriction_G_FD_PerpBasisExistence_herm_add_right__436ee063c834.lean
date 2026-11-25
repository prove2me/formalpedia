-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_add_right__436ee063c834
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_add_right__436ee063c834
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:35.232821+00:00
-- url     : https://prove2.me/theorems/513cca4f-8928-49e7-b136-712338b396c7
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm add right  436ee063c834: P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm add right  436ee063c834
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm add right  436ee063c834 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm add right  436ee063c834 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L16-L18

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ExistsUnitaryBasisSameFlag
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermEqZeroOfTraceFormVanish
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalComplementLines
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpBasisExistence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_add_right__436ee063c834 (G : Matrix (Fin r) (Fin r) E) (x y y' : Fin r → E) :
    herm G x (y + y') = herm G x y + herm G x y' := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«PerpBasisExistence».«herm_add_right'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_add_right__436ee063c834
