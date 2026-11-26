-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volumeReal_rotationalProfile_Ioo
-- name    : Sqrt6KissingBound.volumeReal_rotationalProfile_Ioo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:05:37.378303+00:00
-- url     : https://prove2.me/theorems/367e5758-9a82-471f-9cf4-dfe2ae4d8459
-- title:
--   Sqrt6 Kissing Bound: volume Real rotational Profile Ioo
-- statement:
--   The Sqrt6 Kissing Bound construction uses the volume Real rotational Profile Ioo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegralReal.lean#L25-L36
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegralReal.lean#L25-L36

import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
import Mathlib.MeasureTheory.Measure.Real
import Definitions.Def_Sqrt6KissingBound_ProfileIntegralReal
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real

theorem Sqrt6KissingBound.volumeReal_rotationalProfile_Ioo (d : ℕ) {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 2)))).real
        (rotationalProfile (d + 1) (Set.Ioo a b) g) =
      (∫ t in a..b, g t ^ (d + 1)) * unitBallVolumeReal (d + 1) := by sorry
