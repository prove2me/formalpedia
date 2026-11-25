-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:16:41.716892+00:00
-- url     : https://prove2.me/theorems/1da91ef3-1ade-5c26-9af5-d835aeca8da4
-- title:
--   P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Trace Norm Bounds eq zero of trace  51e3043ae2c7: P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Trace Norm Bounds eq zero
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Trace Norm Bounds eq zero of trace  51e3043ae2c7 construction uses the P2 M Reciprocity Theory Chart Restriction G Arakelov Geometry Trace Norm Bounds eq zero of trace  51e3043ae2c7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/XZeroPowDvdOfIsHomogeneousAeval.lean#L192-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovGeometry/XZeroPowDvdOfIsHomogeneousAeval.lean#L192-L210

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_BasisOfLinearIndependentOfCardEqFinrank
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_XZeroPowDvdOfIsHomogeneousAeval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_mul_mem_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_sec_div_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module
variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7 [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n)
    (h0 : ∀ l, ((Algebra.trace (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
        ⟨s * ε l / x (e 0) ^ (n + k), sec_div_mem x (e 0) (mul_mem_sec x hs (hε l))⟩ :
          fnField (x ∘ e)) : Ω) = 0) : s = 0 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«ArakelovGeometry».«TraceNormBounds».«eq_zero_of_trace'» := P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_TraceNormBounds_eq_zero_of_trace__51e3043ae2c7
