-- Prove2me | Theorems.Thm_QECCertificates_mem_matRowList
-- name    : QECCertificates.mem_matRowList
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:48:54.648677+00:00
-- url     : https://prove2.me/theorems/84c0de48-a125-4848-8beb-0a12384301f0
-- title:
--   QECCertificates: mem mat Row List
-- statement:
--   The QECCertificates construction uses the mem mat Row List property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L90-L92
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L90-L92

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCompression
public import Definitions.Def_LeanPool_QECCertificates_GF2_Canonical
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_HGPCleaning
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {r₁ n₁ r₂ n₂ : ℕ}

theorem QECCertificates.mem_matRowList {m k : ℕ} {M : Matrix (Fin m) (Fin k) (ZMod 2)} {y : Vec k} :
    y ∈ matRowList M ↔ ∃ i, (fun j => M i j) = y := by sorry
