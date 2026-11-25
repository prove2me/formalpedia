-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscLat_gram_mul
-- name    : ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.gram_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:36:41.170227+00:00
-- url     : https://prove2.me/theorems/53314967-59e1-44f0-ab62-0e49530bb260
-- title:
--   HDisc Lat: gram mul
-- statement:
--   The HDisc Lat construction uses the gram mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/HDiscAA.lean#L44-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscLat
open Module

theorem ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.gram_mul {F L : Type*} [Field F] [Field L] [Algebra F L] {κ : Type*} [Fintype κ]
    [DecidableEq κ] (a : Basis κ F L) (h : L) :
    (Matrix.of fun p q => Algebra.trace F L (h * a p * a q)).det =
      Algebra.norm F h * Algebra.discr F a := by sorry
