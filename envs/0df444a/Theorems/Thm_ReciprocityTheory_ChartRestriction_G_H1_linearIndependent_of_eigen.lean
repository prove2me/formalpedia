-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_linearIndependent_of_eigen
-- name    : ReciprocityTheory.ChartRestriction.G.H1.linearIndependent_of_eigen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:25:39.758244+00:00
-- url     : https://prove2.me/theorems/70377616-ee5d-57e8-9088-7950e52d1590
-- title:
--   H1: linear Independent of eigen
-- statement:
--   The H1 construction uses the linear Independent of eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/NakayamaChar.lean#L8-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/NakayamaChar.lean#L8-L12

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ReducedBasisStatement
import Definitions.Def_Lemmata_GeneralBFactExtra_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_NakayamaChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.H1
open Module TensorProduct

theorem ReciprocityTheory.ChartRestriction.G.H1.linearIndependent_of_eigen {K V ι Γ : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Γ → V →ₗ[K] V) (c : ι → Γ → K) (w : ι → V) (hw : ∀ i, w i ≠ 0)
    (he : ∀ i γ, T γ (w i) = c i γ • w i) (hd : ∀ i j, i ≠ j → ∃ γ, c i γ ≠ c j γ) :
    LinearIndependent K w := by sorry
