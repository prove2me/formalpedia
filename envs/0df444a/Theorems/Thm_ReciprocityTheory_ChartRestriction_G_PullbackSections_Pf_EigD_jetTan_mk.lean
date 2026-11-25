-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigD_jetTan_mk
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetTan_mk
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:33.348237+00:00
-- url     : https://prove2.me/theorems/94044306-bbb6-47f8-ad95-cae8c2514a38
-- title:
--   Eig D: jet Tan mk
-- statement:
--   The Eig D construction uses the jet Tan mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SubstTanSnd.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/SubstTanSnd.lean#L21-L23

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SingleMemDegLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_SubstTanSnd
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G
attribute [local instance] Over.cartesianMonoidalCategory
variable {V : Type} [CommRing V] {d : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.jetTan_mk {ι : Type} [DecidableEq ι] (ℓ : ι) (q : MvPolynomial ι V) :
    jetTan (R := V) (m := 0) ℓ (Ideal.Quotient.mk _ q) =
      aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) q := by sorry
