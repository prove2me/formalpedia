-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_isPreconnected_upper
-- name    : ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:36.174613+00:00
-- url     : https://prove2.me/theorems/68d0021d-166c-446d-958f-ad6560964895
-- title:
--   GGC: is Preconnected upper
-- statement:
--   The GGC construction uses the is Preconnected upper property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L248-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/GGConnA.lean#L248-L258

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}

theorem ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper {ι : Type*} [Fintype ι] :
    IsPreconnected {b : ι → Matrix (Fin r) (Fin r) ℂ |
      ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b i a c = 0} := by sorry
