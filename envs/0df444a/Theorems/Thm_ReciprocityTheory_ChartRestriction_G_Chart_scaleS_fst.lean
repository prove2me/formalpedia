-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_scaleS_fst
-- name    : ReciprocityTheory.ChartRestriction.G.Chart.scaleS_fst
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:05:15.378713+00:00
-- url     : https://prove2.me/theorems/6d0eaceb-17d0-5424-a933-dc439309bd29
-- title:
--   Chart: scale S fst
-- statement:
--   The Chart construction uses the scale S fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/TanLoc.lean#L26-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
import Definitions.Def_Lemmata_MiscLemmasQ_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanLoc
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {S : Type} [CommRing S] {B : Type} [CommRing B] [Algebra S B]

theorem ReciprocityTheory.ChartRestriction.G.Chart.scaleS_fst {A : Type} [CommRing A] [Algebra S A] (c : A) (x : DualNumber A) : (scaleS (S := S) c x).fst = x.fst := by sorry
