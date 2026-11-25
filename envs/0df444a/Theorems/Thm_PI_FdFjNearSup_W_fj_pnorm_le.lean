-- Prove2me | Theorems.Thm_PI_FdFjNearSup_W_fj_pnorm_le
-- name    : PI.FdFjNearSup.W.fj_pnorm_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:29:36.74114+00:00
-- url     : https://prove2.me/theorems/53c43d0a-effe-4ac2-a542-ef2802d24f75
-- title:
--   W: fj pnorm le
-- statement:
--   The W construction uses the fj pnorm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L87-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean#L87-L126

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

theorem PI.FdFjNearSup.W.fj_pnorm_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (C : ℝ) (hC0 : 0 ≤ C)
    (hflow : ∀ x ∈ X.dom, ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom ∧
      X.nfac la (X.flow ξ (fun τ => (s τ : ℂ)) x) = X.nfac la x)
    (hP : ∀ x ∈ X.dom, X.pnorm la P x ≤ C) :
    ∀ x ∈ X.dom, X.pnorm la (X.fj la ξ ν P) x ≤ C := by sorry
