-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_ImaginaryMajorants_jp_col
-- name    : ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.jp_col
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:18:46.94292+00:00
-- url     : https://prove2.me/theorems/25129728-81f5-5093-8f85-b08e80412428
-- title:
--   Imaginary Majorants: jp col
-- statement:
--   The Imaginary Majorants construction uses the jp col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ImaginaryMajorants.lean#L16-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/ImaginaryMajorants.lean#L16-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoostLowerBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ImaginaryMajorants
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
open ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants
open MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds
variable {r : ℕ} (X : Data E r)

theorem ReciprocityTheory.ChartRestriction.G.FD.ImaginaryMajorants.jp_col {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (d : Fin X.p0) :
    X.jp z τ (X.colP z τ d) = X.colP z τ d := by sorry
