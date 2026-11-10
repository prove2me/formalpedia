-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat27_smeared_exponent_public
-- name    : ProbabilityTheory.leanlevy_chat27_smeared_exponent_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:18:22.374634+00:00
-- url     : https://prove2.me/theorems/1db84259-c173-407b-bd65-aa65a5abb3af
-- title:
--   Public source-backed Levy-Khintchine smearing identity
-- statement:
--   Source-exact identity relating the averaged Levy-Khintchine exponent to the characteristic function of the finite smeared measure, with all dependencies public and available.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineUniqueness.lean original smeared_exponent_eq_charFun; previously accepted private original target 3bfe7028 as candidate 32098. Necessary public adapter for wrapper triple uniqueness.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_intInt_exponent_jump
import Theorems.Thm_ProbabilityTheory_continuous_integral_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_charFun_smearedMeasure_public

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat27_smeared_exponent_public
    (T : LevyKhintchineTriple) (ξ : ℝ) :
    T.exponent ξ - (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1, T.exponent (ξ + u)
      = charFun (smearedMeasure T.gaussianVariance T.levyMeasure) ξ := by sorry
