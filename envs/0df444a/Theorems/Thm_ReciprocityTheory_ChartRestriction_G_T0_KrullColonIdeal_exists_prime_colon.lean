-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_KrullColonIdeal_exists_prime_colon
-- name    : ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal.exists_prime_colon
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:36:06.319803+00:00
-- url     : https://prove2.me/theorems/c1d757d9-3a16-5312-b73c-5c269a6e0f95
-- title:
--   Krull Colon Ideal: exists prime colon
-- statement:
--   The Krull Colon Ideal construction uses the exists prime colon property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L25-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L25-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegKrull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal
variable {R : Type*} [CommRing R]

theorem ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal.exists_prime_colon [IsNoetherianRing R] (s a : R) (ha : a ∉ Ideal.span {s}) :
    ∃ b : R, b ∉ Ideal.span {s} ∧ colonI s a ≤ colonI s b ∧
      ∀ q1 q2 : R, q1 * q2 ∈ colonI s b → q1 ∈ colonI s b ∨ q2 ∈ colonI s b := by sorry
