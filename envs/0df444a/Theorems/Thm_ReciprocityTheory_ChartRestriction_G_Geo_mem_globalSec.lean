-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_globalSec
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mem_globalSec
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:46.142158+00:00
-- url     : https://prove2.me/theorems/1e1beaee-bbfb-5573-84c4-6142d89f83c0
-- title:
--   Geo: mem global Sec
-- statement:
--   The Geo construction uses the mem global Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/Bundle.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/Bundle.lean#L34-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
variable (o : Type*) {Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {ι : Type*}
variable {o}

theorem ReciprocityTheory.ChartRestriction.G.Geo.mem_globalSec {x : ι → Ω} {r : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o x r E) (e : E) :
    e ∈ globalSec B ↔ ∀ i, x i ≠ 0 → e ∈ B.lat i := by sorry
