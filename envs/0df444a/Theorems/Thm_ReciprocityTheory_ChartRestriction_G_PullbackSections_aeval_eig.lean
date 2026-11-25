-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_aeval_eig
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_eig
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:32:37.205235+00:00
-- url     : https://prove2.me/theorems/b723f7c9-9f99-41af-b230-88f07de62cc0
-- title:
--   Pullback Sections: aeval eig
-- statement:
--   The Pullback Sections construction uses the aeval eig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/LieBridgeB.lean#L21-L25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.aeval_eig (f : Module.End S M) {x : S} {m : M} (hm : f m = x • m) (P : ℤ[X]) :
    aeval f P m = aeval x P • m := by sorry
