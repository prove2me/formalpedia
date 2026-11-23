-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_KrullColonIdeal_mem_colonI
-- name    : ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal.mem_colonI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:24.758714+00:00
-- url     : https://prove2.me/theorems/81b1aa8d-930d-49d8-90fc-216069571496
-- title:
--   Krull Colon Ideal: mem colon I
-- statement:
--   The Krull Colon Ideal construction uses the mem colon I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegKrull.lean#L23-L23

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

theorem ReciprocityTheory.ChartRestriction.G.T0.KrullColonIdeal.mem_colonI {s c r : R} : r ∈ colonI s c ↔ r * c ∈ Ideal.span {s} := by sorry
