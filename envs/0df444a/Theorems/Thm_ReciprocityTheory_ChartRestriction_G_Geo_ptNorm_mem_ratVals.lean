-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_ptNorm_mem_ratVals
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_mem_ratVals
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:13:43.816661+00:00
-- url     : https://prove2.me/theorems/515c67a4-6939-5920-bde6-52907832298c
-- title:
--   Geo: pt Norm mem rat Vals
-- statement:
--   The Geo construction uses the pt Norm mem rat Vals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenVol.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/PenVol.lean#L39-L45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_PenVol
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
open MvPolynomial Filter
variable {o : Type*} [CommRing o] {Ω : Type*} [CommRing Ω] [Algebra o Ω] {ι : Type*}

theorem ReciprocityTheory.ChartRestriction.G.Geo.ptNorm_mem_ratVals (m : ConeMetric ℂ ι) (σ : o →+* ℂ) (x : ι → Ω) {τ : ℕ}
    {f : MvPolynomial ι o} (hf : f ∈ homogeneousSubmodule ι o τ) {z : ι → ℂ}
    (hz : z ∈ conePts σ (coordIdeal o x)) :
    ptNorm m σ τ f z ∈ ratVals m σ x τ (aeval x f) := by sorry
