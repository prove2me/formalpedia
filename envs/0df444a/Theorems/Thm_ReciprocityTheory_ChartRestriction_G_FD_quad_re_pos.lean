-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_pos
-- name    : ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:14.869603+00:00
-- url     : https://prove2.me/theorems/f87e0b7e-9a3b-4fe5-8bcc-def6ead5ccbe
-- title:
--   FD: quad re pos
-- statement:
--   The FD construction uses the quad re pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L163-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L163-L171

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

theorem ReciprocityTheory.ChartRestriction.G.FD.quad_re_pos {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosDef) {c : Fin n → ℂ}
    (hc : c ≠ 0) : 0 < (∑ a, ∑ b, c a * M a b * conj (c b)).re := by sorry
