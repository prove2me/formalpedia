-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BlockIdentityExpansion_f_gram_re
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion.f_gram_re
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:58.833354+00:00
-- url     : https://prove2.me/theorems/9e880a07-b7e8-5cd1-b5d8-83c413df41a4
-- title:
--   Block Identity Expansion: f gram re
-- statement:
--   The Block Identity Expansion construction uses the f gram re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BlockIdentityExpansion.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BlockIdentityExpansion.lean#L38-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveSpanMatrices
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BlockIdentityExpansion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PositiveSpanMatrices
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.FD.BlockIdentityExpansion.f_gram_re (X : Data E r) (ξ : Fin r → E) (z0 : Frame X.Ψ r) (f : X.Ψ → Fin (r - 2) → Fin r → ℂ)
    (hf : X.UBasis z0 ξ f) (τ : X.Ψ) (a : Fin (r - 2) → ℂ) :
    (hermC τ.1 X.Gm (∑ k, a k • f τ k) (∑ k, a k • f τ k)).re =
      ∑ k : Fin (r - 2), if (k : ℕ) < X.p0 - 1 then ‖a k‖ ^ 2 else -‖a k‖ ^ 2 := by sorry
