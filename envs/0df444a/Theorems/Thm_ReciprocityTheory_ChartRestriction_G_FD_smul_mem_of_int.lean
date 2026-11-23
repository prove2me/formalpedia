-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_smul_mem_of_int
-- name    : ReciprocityTheory.ChartRestriction.G.FD.smul_mem_of_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:49:23.877973+00:00
-- url     : https://prove2.me/theorems/df7e79f6-b865-40b2-ab9a-567c7de45f91
-- title:
--   FD: smul mem of int
-- statement:
--   The FD construction uses the smul mem of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/DiscrMulHermitianIntegral.lean#L20-L24

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MmatMulVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscrMulHermitianIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex Module Matrix
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem ReciprocityTheory.ChartRestriction.G.FD.smul_mem_of_int {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E)) {c : E} (hc : IsIntegral ℤ c)
    {v : Fin r → E} (hv : v ∈ L) : c • v ∈ L := by sorry
