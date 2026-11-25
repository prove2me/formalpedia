-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FinrankRieszBounds_maj_csmul
-- name    : ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.maj_csmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:29:55.422801+00:00
-- url     : https://prove2.me/theorems/50ec60ec-212f-42da-8341-00711c5518f1
-- title:
--   Finrank Riesz Bounds: maj csmul
-- statement:
--   The Finrank Riesz Bounds construction uses the maj csmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankRieszBounds.lean#L12-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FinrankRieszBounds.lean#L12-L38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DiscreteLatticeMinimum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FinrankRieszBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds
open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem ReciprocityTheory.ChartRestriction.G.FD.FinrankRieszBounds.maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by sorry
