-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_smul_left
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:36:22.487851+00:00
-- url     : https://prove2.me/theorems/d9bae9d3-47f6-45e0-ad2e-7d1b4f7031fa
-- title:
--   Hermitian Trace Form Vanishing: herm smul left
-- statement:
--   The Hermitian Trace Form Vanishing construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L34-L36

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Lemmata_GeneralBFactAltForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianTraceFormVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing
open NumberField ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by sorry
