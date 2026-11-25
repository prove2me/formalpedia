-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_eps__sq_825dc2e87748
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_eps__sq_825dc2e87748
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:51.810048+00:00
-- url     : https://prove2.me/theorems/f527d8f5-4208-450a-89cb-534a75b60f34
-- title:
--   P2 M Reciprocity Theory Chart Restriction G FD Perp Component Combination eps  sq 825dc2e87748: P2 M Reciprocity Theory Chart Restriction G FD Perp Component Combination eps  sq 825dc2e87748
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G FD Perp Component Combination eps  sq 825dc2e87748 construction uses the P2 M Reciprocity Theory Chart Restriction G FD Perp Component Combination eps  sq 825dc2e87748 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpComponentCombination.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/PerpComponentCombination.lean#L17-L19

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpLatticeTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalLatticeDecomposition
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PerpComponentCombination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpComponentCombination
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PerpBasisExistence
  ReciprocityTheory.ChartRestriction.G.FD.PerpLatticeTransfer
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_eps__sq_825dc2e87748 (p : ℕ) {n : ℕ} (k : Fin n) : eps' p k * eps' p k = 1 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«FD».«PerpComponentCombination».«eps'_sq» := P2M_ReciprocityTheory_ChartRestriction_G_FD_PerpComponentCombination_eps__sq_825dc2e87748
