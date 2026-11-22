-- Prove2me | Theorems.Thm_QECCertificates_hgp_X_distance_ge
-- name    : QECCertificates.hgp_X_distance_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:30.906843+00:00
-- url     : https://prove2.me/theorems/9cc64b81-27a2-4da9-bb51-c8bd2b19c912
-- title:
--   QECCertificates: hgp X distance ge
-- statement:
--   **X distance lower bound for the HGP (the cleaning theorem)**: a nonzero X-type operator outside
--   the row space of `H_Z`, that is a nontrivial X-type logical operator, has weight at least
--   $\min(d_1, d_2^\top)$, the smaller of the left code distance and the transposed code distance.
--
--   This is complementary to the single-block lower bounds of the second part: those need no "outside
--   the row space" hypothesis, whereas this theorem also covers **mixed blocks** (both blocks nonzero
--   at once), at the cost of being stated in the quotient.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L574-L616
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L574-L616

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

theorem QECCertificates.hgp_X_distance_ge (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2))
    (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ d₂T : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hd₂ : ∀ w : Vec r₂, w ≠ 0 → H₂.transpose *ᵥ w = 0 → d₂T ≤ hammingNorm w) :
    min d₁ d₂T ≤ hammingNorm v := by sorry
