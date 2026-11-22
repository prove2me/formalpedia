-- Prove2me | Theorems.Thm_QECCertificates_mem_kerL
-- name    : QECCertificates.mem_kerL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:45:18.4328+00:00
-- url     : https://prove2.me/theorems/09ad8613-2c11-44a6-9710-25834443d16c
-- title:
--   QECCertificates: mem ker L
-- statement:
--   The QECCertificates construction uses the mem ker L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L107-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/KernelBasis.lean#L107-L108

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.mem_kerL {L : List (Vec n)} {x : Vec n} :
    x ∈ kerL L ↔ ∀ r ∈ L, r ⬝ᵥ x = 0 := by sorry
