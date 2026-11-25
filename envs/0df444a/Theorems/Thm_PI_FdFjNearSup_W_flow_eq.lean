-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_flow_eq
-- name    : PI.FdFjNearSup.W.flow_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:47.049424+00:00
-- url     : https://prove2.me/theorems/49b81164-2a17-40ba-90a2-2a3fae9dc092
-- title:
--   W: flow eq
-- statement:
--   The W construction uses the flow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L66-L67

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

theorem PI.FdFjNearSup.W.flow_eq {r : ℕ} (X : Data E r) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flowV (X.embV ξ) s x := by sorry
