-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:14:56.70333+00:00
-- url     : https://prove2.me/theorems/530d7334-c60d-5b35-96e5-7d71cbc06679
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib deh eval  rename 376a9ee8007e: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib deh eval  rename 376a9ee8007e
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib deh eval  rename 376a9ee8007e construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Fib deh eval  rename 376a9ee8007e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/FibreStB.lean#L17-L27

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_FibreStB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.Fib
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
variable {ι : Type} [Fintype ι] {Ω : Type*} [Field Ω] {D : ℕ} {x : ι → Ω} {e : Fin (D + 1) → ι}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e {S : Type*} [Field S] (v : ι → S) (e : Fin (D + 1) → ι)
    (Θ : MvPolynomial ι ℤ) (H : Polynomial (MvPolynomial (Fin (D + 1)) ℤ)) :
    deh v (e 0) (H.eval₂ (rename e : MvPolynomial _ ℤ →ₐ[ℤ] MvPolynomial ι ℤ).toRingHom Θ) =
      H.eval₂ (deh (v ∘ e) 0) (deh v (e 0) Θ) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«Fib».«deh_eval₂_rename» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_Fib_deh_eval__rename_376a9ee8007e
