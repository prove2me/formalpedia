-- Prove2me | Theorems.Thm_Sqrt6KissingBound_volume_rotationalProfile_Ioo
-- name    : Sqrt6KissingBound.volume_rotationalProfile_Ioo
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:04:39.940115+00:00
-- url     : https://prove2.me/theorems/5f8082ec-2bf9-45c1-9953-86f790d1579c
-- title:
--   Sqrt6 Kissing Bound: volume rotational Profile Ioo
-- statement:
--   For a nonnegative continuous profile on an interval, the volume is the
--   transverse unit-ball volume times the elementary one-dimensional integral.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegral.lean#L25-L54
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/ProfileIntegral.lean#L25-L54

import Definitions.Def_Sqrt6KissingBound_ProfileVolume
import Definitions.Def_Sqrt6KissingBound_ProfileIntegral
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory intervalIntegral
open scoped ENNReal Interval Real

theorem Sqrt6KissingBound.volume_rotationalProfile_Ioo (d : ℕ) {a b : ℝ} (hab : a ≤ b)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hg0 : ∀ t ∈ Set.Icc a b, 0 ≤ g t) :
    (volume : Measure (EuclideanSpace ℝ (Fin (d + 2))))
        (rotationalProfile (d + 1) (Set.Ioo a b) g) =
      ENNReal.ofReal (∫ t in a..b, g t ^ (d + 1)) *
        unitBallVolume (d + 1) := by sorry
