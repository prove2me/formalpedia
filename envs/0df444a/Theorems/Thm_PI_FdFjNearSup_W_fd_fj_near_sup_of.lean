-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_fd_fj_near_sup_of
-- name    : PI.FdFjNearSup.W.fd_fj_near_sup_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:34.230827+00:00
-- url     : https://prove2.me/theorems/54f843c5-f78f-440b-b697-7ebd4e907bd9
-- title:
--   W: fd fj near sup of
-- statement:
--   The W construction uses the fd fj near sup of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L153-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L153-L290

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem PI.FdFjNearSup.W.fd_fj_near_sup_of (h1 : FlowDomainCriterion (E := E)) (h2 : FjHolo (E := E))
    (h3 : FjRealFlow (E := E)) (h4 : OrthonormalFlagTranslate (E := E)) :
    HolomorphicPeriodicityExtension (E := E) → FlowNormRatio (E := E) → ModerateCoefficientPositivity (E := E) →
      NearSupremumTransference (E := E) := by sorry
