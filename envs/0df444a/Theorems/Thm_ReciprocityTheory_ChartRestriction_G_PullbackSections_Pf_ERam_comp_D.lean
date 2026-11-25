-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_comp_D
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.comp_D
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:34:45.119042+00:00
-- url     : https://prove2.me/theorems/6277d584-cc91-49e1-b8bd-51b0208a86bc
-- title:
--   ERam: comp D
-- statement:
--   The ERam construction uses the comp D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamData.lean#L120-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamData.lean#L120-L163

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.comp_D {k : Type} [Field k] [CharZero k] {Ty : Type} [Fintype Ty] (ψ : Ty → E →+* k)
    (htr : ∀ x : E, ∑ t, ψ t x = algebraMap ℚ k (Algebra.trace ℚ E x)) (N : ℕ) (hN : N ≠ 0)
    (hδ : ∀ i, IsIntegral ℤ (((N : 𝓞 E) : E) * omDF (E := E) i)) {d : ℕ} (M : 𝓞 E →+* Matrix (Fin d) (Fin d) k) :
    ∑ t, actD M (bD (N : 𝓞 E) hδ) (cD (ψ t) (N : 𝓞 E)) = 1 := by sorry
