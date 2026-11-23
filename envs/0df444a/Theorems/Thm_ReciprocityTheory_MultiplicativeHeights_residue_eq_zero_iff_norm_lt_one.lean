-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_residue_eq_zero_iff_norm_lt_one
-- name    : ReciprocityTheory.MultiplicativeHeights.residue_eq_zero_iff_norm_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:40.307804+00:00
-- url     : https://prove2.me/theorems/74fb37c5-52f4-4130-8b5b-f8b17c3a19b3
-- title:
--   Multiplicative Heights: residue eq zero iff norm lt one
-- statement:
--   The Multiplicative Heights construction uses the residue eq zero iff norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L20-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ExistsTorusPointOneLeNormSum.lean#L20-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial

theorem ReciprocityTheory.MultiplicativeHeights.residue_eq_zero_iff_norm_lt_one {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : unitBallRing K) :
    IsLocalRing.residue (unitBallRing K) x = 0 ↔ ‖(x : K)‖ < 1 := by sorry
