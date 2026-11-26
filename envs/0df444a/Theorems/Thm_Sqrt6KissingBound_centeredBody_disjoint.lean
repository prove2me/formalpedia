-- Prove2me | Theorems.Thm_Sqrt6KissingBound_centeredBody_disjoint
-- name    : Sqrt6KissingBound.centeredBody_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T06:09:11.248007+00:00
-- url     : https://prove2.me/theorems/efa731b9-9f2a-4f1a-a9a1-f45add979243
-- title:
--   Sqrt6 Kissing Bound: centered Body disjoint
-- statement:
--   The Sqrt6 Kissing Bound construction uses the centered Body disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L63-L72
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L63-L72

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.centeredBody_disjoint {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))}
    (hS : S ⊆ strictCone (standardAxis (k + 1)) ∩ ball 0 1)
    {x z : EuclideanSpace ℝ (Fin (k + 2))}
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    (hxz : inner ℝ x z ≤ (1 : ℝ) / 2) :
    Disjoint (centeredBody k S x) (centeredBody k S z) := by sorry
