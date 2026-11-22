-- Prove2me | Theorems.Thm_QECCertificates_LRAT_chainsFrom_vars_lt
-- name    : QECCertificates.LRAT.chainsFrom_vars_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:00:08.8165+00:00
-- url     : https://prove2.me/theorems/25e75580-ace5-41ff-bf76-f0d5264fcdc3
-- title:
--   LRAT: chains From vars lt
-- statement:
--   The clause variables of a sequence of chains all lie below the exit counter of **that
--   segment**.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L945-L987
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/Reflect/Complete.lean#L945-L987

module
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Encode
public import Definitions.Def_LeanPool_QECCertificates_Reflect_Complete
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates QECCertificates.LRAT

theorem QECCertificates.LRAT.chainsFrom_vars_lt {f : Nat → Nat} {rows : List (List Nat)} {c : Nat}
    (hne : ∀ r ∈ rows, r ≠ [])
    (hlt : ∀ r ∈ rows, ∀ t ∈ r, f t < c) :
    ∀ C ∈ (chainsFrom f rows c).1, ∀ l ∈ C, l.1 < (chainsFrom f rows c).2 := by sorry
