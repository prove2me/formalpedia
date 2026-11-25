-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_of_qmap_mem_qIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.mem_of_qmap_mem_qIdeal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:24:23.81963+00:00
-- url     : https://prove2.me/theorems/97456dfb-d2e8-424a-8959-1d9254919222
-- title:
--   Geo: mem of qmap mem q Ideal
-- statement:
--   The Geo construction uses the mem of qmap mem q Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L61-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterGoodB.lean#L61-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
variable {σ : Type}

theorem ReciprocityTheory.ChartRestriction.G.Geo.mem_of_qmap_mem_qIdeal (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {f : MvPolynomial σ ℤ}
    (hf : qmap f ∈ qIdeal P) : f ∈ P := by sorry
