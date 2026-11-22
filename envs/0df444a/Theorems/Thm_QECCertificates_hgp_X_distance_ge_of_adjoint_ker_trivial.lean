-- Prove2me | Theorems.Thm_QECCertificates_hgp_X_distance_ge_of_adjoint_ker_trivial
-- name    : QECCertificates.hgp_X_distance_ge_of_adjoint_ker_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:54:51.4684+00:00
-- url     : https://prove2.me/theorems/0c8eb7f5-3853-4d40-b41e-16c6631ec627
-- title:
--   QECCertificates: hgp X distance ge of adjoint ker trivial
-- statement:
--   **Lower bound for $d_X$, the branch where the certificate kernel is trivial**: if
--   $\ker H_1^\top = 0$, then every X-type logical operator has weight $\ge d_1$.
--
--   **Which gap this fills**: the cleaning lower bound `hgp_X_distance_ge` gives $\min(d_1,d_2^\top)$,
--   and $d_2^\top$ may be **strictly smaller yet unattainable**; "the certificate kernel of the right
--   route is trivial" ($\ker H_1^\top=0$) is exactly that situation. The theorem says that the smaller
--   value then **does not participate** in the lower bound and $d_1$ alone suffices.
--
--   **Proof** (isomorphic to the cleaning lower bound, but using only **row cleaning** plus a
--   **surjectivity**): suppose $|v|<d_1$. Row cleaning gives $U = C\,H_2$ (where $U$ is `blockL v`), so
--   the remainder $\rho := R + H_1C$ satisfies $\rho H_2 = 0$. Now $\ker H_1^\top = 0$ together with
--   the separation lemma `mem_spanL_of_forall_dot_eq_zero` gives that **the columns of $H_1$ are
--   surjective** (every vector of `Vec r₁` lies in the span of $\mathrm{colList}\,H_1$), so every
--   column of $\rho$ lies there too. Both conditions are met, and `exists_cleaning_cert` gives $D$ with
--   $H_1D = \rho$ and $DH_2 = 0$, so `v` and `(C+D)` form a stabilizer and $v$ lies in the row space,
--   contradicting that $v$ is not a logical operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L861-L870
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/HGPCleaning.lean#L861-L870

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

theorem QECCertificates.hgp_X_distance_ge_of_adjoint_ker_trivial
    (H₁ : Matrix (Fin r₁) (Fin n₁) (ZMod 2)) (H₂ : Matrix (Fin r₂) (Fin n₂) (ZMod 2))
    {v : (Fin n₁ × Fin n₂) ⊕ (Fin r₁ × Fin r₂) → ZMod 2}
    (hv : hgpHX H₁ H₂ *ᵥ v = 0)
    (hlog : v ∉ (hgpHZ H₁ H₂).certificateRowSpace) {d₁ : ℕ}
    (hd₁ : ∀ w : Vec n₁, w ≠ 0 → H₁ *ᵥ w = 0 → d₁ ≤ hammingNorm w)
    (hT : ∀ u : Vec r₁, H₁.transpose *ᵥ u = 0 → u = 0) :
    d₁ ≤ hammingNorm v := by sorry
