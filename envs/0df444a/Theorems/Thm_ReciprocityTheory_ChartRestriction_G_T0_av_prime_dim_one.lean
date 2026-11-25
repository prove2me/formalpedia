-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_prime_dim_one
-- name    : ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:37:14.947093+00:00
-- url     : https://prove2.me/theorems/f434789b-8bb6-44bb-9696-1ad497bea0d6
-- title:
--   T0: av prime dim one
-- statement:
--   The T0 construction uses the av prime dim one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AvPrimeDimOne.lean#L95-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AvPrimeDimOne.lean#L95-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.av_prime_dim_one {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hdim : 1 ≤ ringKrullDim R) (h : R) (hh : h ≠ 0) :
    ∃ p : Ideal R, p.IsPrime ∧ ringKrullDim (R ⧸ p) = 1 ∧ h ∉ p := by sorry
