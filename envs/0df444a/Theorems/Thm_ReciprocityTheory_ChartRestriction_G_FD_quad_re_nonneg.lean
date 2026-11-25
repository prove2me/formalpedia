-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.FD.quad_re_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:21:35.39807+00:00
-- url     : https://prove2.me/theorems/af2d6891-ce9e-4ce8-8b98-7bf1d3d0272d
-- title:
--   FD: quad re nonneg
-- statement:
--   The FD construction uses the quad re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L173-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/LminorSubmatrixCastSucc.lean#L173-L180

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

theorem ReciprocityTheory.ChartRestriction.G.FD.quad_re_nonneg {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (c : Fin n → ℂ) :
    0 ≤ (∑ a, ∑ b, c a * M a b * conj (c b)).re := by sorry
