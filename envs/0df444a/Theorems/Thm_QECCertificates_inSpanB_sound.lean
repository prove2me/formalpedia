-- Prove2me | Theorems.Thm_QECCertificates_inSpanB_sound
-- name    : QECCertificates.inSpanB_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:25.239224+00:00
-- url     : https://prove2.me/theorems/b7e885d7-2777-4b8f-83eb-c7d315c6453f
-- title:
--   QECCertificates: in Span B sound
-- statement:
--   **Soundness**: if `inSpanB` reports true then `v` really lies in the row space.
--
--   Immediate from `add_reduceAgainst_mem` (`v` plus the reduced vector lies in the row space)
--   once the reduced vector is zero.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L160-L167
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean#L160-L167

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Definitions.Def_LeanPool_QECCertificates_GF2_Membership
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.inSpanB_sound {L : List (Vec n)} {v : Vec n} (h : inSpanB L v = true) :
    v ∈ spanL L := by sorry
