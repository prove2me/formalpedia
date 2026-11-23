-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_left__9bdb38af119e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_left__9bdb38af119e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:26:29.672803+00:00
-- url     : https://prove2.me/theorems/feb3292f-6653-4bd4-ac97-a186b3e2fd02
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum left  9bdb38af119e: P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum left  9bdb38af119e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum left  9bdb38af119e construction uses the P2 M Reciprocity Theory Chart Restriction G FD Perp Basis Existence herm sum left  9bdb38af119e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpBasisExistence.lean#L20-L25

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_left__9bdb38af119e (G : Matrix (Fin r) (Fin r) E) {ι : Type*} (s : Finset ι)
    (f : ι → Fin r → E) (y : Fin r → E) : herm G (∑ i ∈ s, f i) y = ∑ i ∈ s, herm G (f i) y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«PerpBasisExistence».«herm_sum_left'» := P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpBasisExistence_herm_sum_left__9bdb38af119e
