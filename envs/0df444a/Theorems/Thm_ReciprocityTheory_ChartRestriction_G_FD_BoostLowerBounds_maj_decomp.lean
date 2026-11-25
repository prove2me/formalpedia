-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_BoostLowerBounds_maj_decomp
-- name    : ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.maj_decomp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:11:50.166056+00:00
-- url     : https://prove2.me/theorems/1ce9d679-ad4f-5f20-a65b-d19fa246667b
-- title:
--   Boost Lower Bounds: maj decomp
-- statement:
--   The Boost Lower Bounds construction uses the maj decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L208-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/BoostLowerBounds.lean#L208-L222

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RankOneBoostIsometries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries
variable {r : ℕ} (X : Data E r) (τ : X.Ψ) {z : Frame X.Ψ r} (hz : z ∈ X.dom) {e : Fin r → ℂ}
include hz

theorem ReciprocityTheory.ChartRestriction.G.FD.BoostLowerBounds.maj_decomp (hee : hermC τ.1 X.Gm e e = 0) (he0 : e ≠ 0) (w0 : Fin r → ℂ)
    (h0e : hermC τ.1 X.Gm w0 e = 0) (h0f : hermC τ.1 X.Gm w0 (X.jp z τ e) = 0) (a b : ℂ) :
    X.maj z τ (w0 + a • e + b • X.jp z τ e) =
      X.maj z τ w0 + (Complex.normSq a + Complex.normSq b) * X.maj z τ e := by sorry
