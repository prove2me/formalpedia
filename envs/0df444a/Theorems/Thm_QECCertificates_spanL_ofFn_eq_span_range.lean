-- Prove2me | Theorems.Thm_QECCertificates_spanL_ofFn_eq_span_range
-- name    : QECCertificates.spanL_ofFn_eq_span_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:01:56.095882+00:00
-- url     : https://prove2.me/theorems/72923959-b0c8-4ebc-b0d9-2c5012ba3cf7
-- title:
--   QECCertificates: span L of Fn eq span range
-- statement:
--   The bridge to the `Set.range` formulation: the row space of `List.ofFn f` is the
--   space spanned by the range of `f`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L184-L190
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basic.lean#L184-L190

module
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.spanL_ofFn_eq_span_range {m : ℕ} (f : Fin m → Vec n) :
    spanL (List.ofFn f) = Submodule.span (ZMod 2) (Set.range f) := by sorry
