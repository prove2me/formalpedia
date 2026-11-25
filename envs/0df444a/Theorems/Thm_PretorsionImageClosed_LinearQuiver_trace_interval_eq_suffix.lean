-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_trace_interval_eq_suffix
-- name    : PretorsionImageClosed.LinearQuiver.trace_interval_eq_suffix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:37:55.204798+00:00
-- url     : https://prove2.me/theorems/a48dd215-5d0e-46d3-a181-e231ef8a12fd
-- title:
--   Linear Quiver: trace interval eq suffix
-- statement:
--   Lemma 6.3: the trace of `M_{c,d}` is the suffix `M_{u,d}` for the least `u ∈ [c, d]` with
--   `M_{u,d} ∈ T`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L132-L145
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L132-L145

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_ImageClosed
public import Definitions.Def_PretorsionImageClosed_Subobjects_Quotients
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Criterion
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_IntervalTraceReject
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement Subcategory
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
variable {T F : Subcategory (Statement.LinRep k n)}

theorem PretorsionImageClosed.LinearQuiver.trace_interval_eq_suffix (hT : T.IsQuotientClosed) {c u d : Fin n} (hcu : c ≤ u)
    (hu : T.prop (interval k u d)) (hmin : ∀ i, c ≤ i → i < u → ¬ T.prop (interval k i d)) :
    T.trace (interval k c d) = suffix c d u hcu := by sorry
