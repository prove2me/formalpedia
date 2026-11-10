-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat27_triple_ext_public
-- name    : ProbabilityTheory.leanlevy_chat27_triple_ext_public
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:21:39.378199+00:00
-- url     : https://prove2.me/theorems/b8123142-f331-47ec-a5b9-a6ef12307e2d
-- title:
--   Public Levy-Khintchine triple exponent injectivity
-- statement:
--   The Levy-Khintchine triple is uniquely recovered from its complex exponent; uses public smearing and finite-measure Fourier injectivity.
-- source:
--   Source-exact public adapter of accepted private canonical target d6f9b1ce candidate 32104; original slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4 LevyKhintchineUniqueness.lean lines 526-546, replacing private smearing premise with the public equivalent chat27.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_smeared_exponent_public
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26b_smearedMeasure_finite_public
import Theorems.Thm_ProbabilityTheory_smearedMeasure_inj

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal Real

theorem ProbabilityTheory.leanlevy_chat27_triple_ext_public
    {T T' : LevyKhintchineTriple}
    (h : ∀ ξ : ℝ, T.exponent ξ = T'.exponent ξ) : T = T' := by sorry
