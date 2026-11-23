-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:45.66336+00:00
-- url     : https://prove2.me/theorems/298be79c-8d2a-4c84-9313-c081117b2c8d
-- title:
--   FD: herm C smul right
-- statement:
--   The FD construction uses the herm C smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L110-L114

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.hermC_smul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u v : Fin r → ℂ) :
    hermC τ G u (c • v) = conj c * hermC τ G u v := by sorry
