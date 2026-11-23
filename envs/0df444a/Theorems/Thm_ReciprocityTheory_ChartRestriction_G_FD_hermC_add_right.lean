-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_add_right
-- name    : ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:08.933491+00:00
-- url     : https://prove2.me/theorems/65fe9b3e-d52a-49e3-8467-c8c4dc78743b
-- title:
--   FD: herm C add right
-- statement:
--   The FD construction uses the herm C add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L105-L108

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

theorem ReciprocityTheory.ChartRestriction.G.FD.hermC_add_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u v v' : Fin r → ℂ) :
    hermC τ G u (v + v') = hermC τ G u v + hermC τ G u v' := by sorry
