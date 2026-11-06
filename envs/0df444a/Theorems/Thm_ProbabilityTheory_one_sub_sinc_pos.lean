-- Prove2me | Theorems.Thm_ProbabilityTheory_one_sub_sinc_pos
-- name    : ProbabilityTheory.one_sub_sinc_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:03:26.303147+00:00
-- url     : https://prove2.me/theorems/65cc9ec6-1d63-41a4-86a5-4a0c4e5fdadc
-- title:
--   LeanLevy: ProbabilityTheory.one_sub_sinc_pos
-- statement:
--   `1 - Real.sinc x` is strictly positive for `x ≠ 0`, since `sin x / x < 1` there. Exact extracted Lean theorem type; proof pending Prove2Me verification. Bochner source-module import replaced by its exact public theorem interface; that theorem's proof remains open.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L1491

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_InfiniteDivisible
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Probability_Characteristic
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Real.Pi.Bounds

theorem ProbabilityTheory.one_sub_sinc_pos : ∀ {x : Real},
  @Ne Real x (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero)) →
    @LT.lt Real Real.instLT (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))
      (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
        (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne)) (Real.sinc x)) := by sorry
