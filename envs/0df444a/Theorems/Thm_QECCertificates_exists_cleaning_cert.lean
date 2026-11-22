-- Prove2me | Theorems.Thm_QECCertificates_exists_cleaning_cert
-- name    : QECCertificates.exists_cleaning_cert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:40.06889+00:00
-- url     : https://prove2.me/theorems/c3fbb6f3-4f09-4291-83c2-583788c34213
-- title:
--   QECCertificates: exists cleaning cert
-- statement:
--   **Cleaning certificate (consistency)**: a matrix `ρ` whose columns all lie in the column space
--       of
--   `H₁` and which satisfies `ρ H₂ = 0` can be written as `H₁ D` with `D H₂ = 0`, that is, it can be
--   cleaned.
--
--   Construction: `D = Σ_{ri} preimage(ri.1) ⊗ (row ri.2 of ρ)`, where `ri` runs over the pivot rows of
--   `rowReduce (colList H₁)` (`col_decomp` supplies the coefficients).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L453-L493
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L453-L493

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

theorem QECCertificates.exists_cleaning_cert {H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)}
    {H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2)} {ρ : Matrix (Fin r₁) (Fin r₂) (ZMod 2)}
    (hcol : ∀ j, (fun i => ρ i j) ∈ spanL (colList H₁))
    (hrow : ρ * H₂ = 0) :
    ∃ D : Matrix (Fin n₁) (Fin r₂) (ZMod 2), H₁ * D = ρ ∧ D * H₂ = 0 := by sorry
