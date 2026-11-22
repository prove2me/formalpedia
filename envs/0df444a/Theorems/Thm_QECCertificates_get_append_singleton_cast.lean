-- Prove2me | Theorems.Thm_QECCertificates_get_append_singleton_cast
-- name    : QECCertificates.get_append_singleton_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:11:45.465798+00:00
-- url     : https://prove2.me/theorems/ff4c8552-4c31-4a3b-9960-6de67965a5d9
-- title:
--   QECCertificates: get append singleton cast
-- statement:
--   The `i`-th element of `(D ++ [x])`, for `i` within `D`, is the `i`-th element of
--   `D`.
--
--   For a variable `D`, `(D ++ [x]).length` is **not** defeq to `D.length + 1`, so the index is
--   written out explicitly as `⟨i.val, _⟩` rather than with `Fin.cast`, which avoids moving
--   proofs around at the level of `Fin`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L262-L265
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankEchelon.lean#L262-L265

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankEchelon
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.get_append_singleton_cast (D : List (PivRow n)) (x : PivRow n) (i : Fin D.length) :
    (D ++ [x]).get ⟨i.val, by have h := length_append_singleton D x; have := i.isLt; omega⟩ =
      D.get i := by sorry
