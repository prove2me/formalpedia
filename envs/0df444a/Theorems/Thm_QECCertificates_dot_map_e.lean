-- Prove2me | Theorems.Thm_QECCertificates_dot_map_e
-- name    : QECCertificates.dot_map_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:02:20.100601+00:00
-- url     : https://prove2.me/theorems/1884cd46-75c0-4e1c-9ddb-aa5f106508de
-- title:
--   QECCertificates: dot map e
-- statement:
--   **Pairing two basis-vector sums**: the value is the parity of the intersection of the
--   two supports. This is the lemma that keeps a check-row comparison at `|A|` terms.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L80-L90
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Basis.lean#L80-L90

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.dot_map_e (A B : List (Fin n)) (hB : B.Nodup) :
    ((A.map e).sum) ⬝ᵥ ((B.map e).sum) = ((A.filter (fun a => a ∈ B)).length : ZMod 2) := by sorry
