-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_herm_single_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_single_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:56.034139+00:00
-- url     : https://prove2.me/theorems/065076bb-33fa-48d4-85df-cc3af47301c0
-- title:
--   Hermitian Trace Form Vanishing: herm single right
-- statement:
--   The Hermitian Trace Form Vanishing construction uses the herm single right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/HermitianTraceFormVanishing.lean#L61-L65

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

theorem ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_single_right (G : Matrix (Fin r) (Fin r) E) (v : Fin r → E) (b : Fin r) :
    herm G v (Pi.single b 1) = (Matrix.vecMul v G) b := by sorry
