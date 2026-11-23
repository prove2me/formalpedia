-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_pnorm_eq
-- name    : PI.FdFjNearSup.W.pnorm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:36:15.164796+00:00
-- url     : https://prove2.me/theorems/e48934d7-6827-4b1b-acdc-f23c5772df5b
-- title:
--   W: pnorm eq
-- statement:
--   The W construction uses the pnorm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L49-L50

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

theorem PI.FdFjNearSup.W.pnorm_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    X.pnorm la Q x = ‖Q x‖ * X.nfac la x := by sorry
