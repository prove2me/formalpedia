-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_rel_zero
-- name    : ReciprocityTheory.ChartRestriction.G.TB.rel_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:42:31.86634+00:00
-- url     : https://prove2.me/theorems/08986680-cfd9-4be0-88ff-e8da9616df51
-- title:
--   TB: rel zero
-- statement:
--   The TB construction uses the rel zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JInjCore.lean#L19-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/JInjCore.lean#L19-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JInjCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB

theorem ReciprocityTheory.ChartRestriction.G.TB.rel_zero {K F C Pt : Type} [Field K] [Field F] [Algebra K F] [IsGalois K F]
    [AddCommGroup C] [Module K C] (v : C →ₗ[K] (Pt → F)) (act : (F ≃ₐ[K] F) → Pt → Pt)
    (hbij : ∀ g, Function.Bijective (act g)) (heq : ∀ g f y, v f (act g y) = g (v f y))
    (hinj : Function.Injective v) {n : ℕ} (b : Fin n → C) (hb : LinearIndependent K b) :
    ∀ (s : Finset (Fin n)) (a : Fin n → F), (∀ y, ∑ i ∈ s, a i * v (b i) y = 0) → ∀ i ∈ s, a i = 0 := by sorry
