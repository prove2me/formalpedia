-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_right__48d7e64a9d84
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_right__48d7e64a9d84
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:42.27501+00:00
-- url     : https://prove2.me/theorems/aa84fcc1-41a5-452f-ac90-59f64bc2c232
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum right  48d7e64a9d84: P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum right  48d7e64a9d84
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum right  48d7e64a9d84 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum right  48d7e64a9d84 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L27-L32

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_right__48d7e64a9d84 (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (x : Fin r → E) : herm G x (∑ i ∈ s, f i) = ∑ i ∈ s, herm G x (f i) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«PerpBasisExistence».«herm_sum_right'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_right__48d7e64a9d84
