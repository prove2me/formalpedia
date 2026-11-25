-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_aeval_tan
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_tan
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:54:07.564965+00:00
-- url     : https://prove2.me/theorems/50a5a646-f2e6-5f6a-beed-0b63404721ae
-- title:
--   Pullback Sections: aeval tan
-- statement:
--   The Pullback Sections construction uses the aeval tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L40-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/HolJetF.lean#L40-L67

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff
variable {Y : Scheme.{0}}
variable {K : Type} [Field K] {ι : Type} [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_tan (ℓ : ι) (q : MvPolynomial ι K) :
    MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber K) else 0) q =
      TrivSqZeroExt.inl (MvPolynomial.constantCoeff q) +
        TrivSqZeroExt.inr (MvPolynomial.coeff (Finsupp.single ℓ 1) q) := by sorry
