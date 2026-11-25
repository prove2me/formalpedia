-- Prove2me | Theorems.Thm_PretorsionImageClosed_LinearQuiver_trace_interval_eq_bot
-- name    : PretorsionImageClosed.LinearQuiver.trace_interval_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:37:21.809472+00:00
-- url     : https://prove2.me/theorems/4bdca4f2-3ee5-5cea-b773-0fe54ef78e82
-- title:
--   Linear Quiver: trace interval eq bot
-- statement:
--   Lemma 6.3: the trace of `M_{c,d}` vanishes when no `M_{u,d}` with `u ∈ [c, d]` lies in `T`.
--
--   Source: https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L148-L153
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/IntervalTraceReject.lean#L148-L153

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

theorem PretorsionImageClosed.LinearQuiver.trace_interval_eq_bot {c d : Fin n}
    (h : ∀ i, c ≤ i → i ≤ d → ¬ T.prop (interval k i d)) : T.trace (interval k c d) = ⊥ := by sorry
