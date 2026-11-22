-- Prove2me | Theorems.Thm_QECCertificates_eq_minWeight_of_bounds
-- name    : QECCertificates.eq_minWeight_of_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:49:48.590608+00:00
-- url     : https://prove2.me/theorems/ea6c93f8-0831-4e56-be0b-54467afaade8
-- title:
--   QECCertificates: eq min Weight of bounds
-- statement:
--   **The exact distance (the two sides together)**: equal lower and upper bounds give a
--   distance exactly equal to $d$.
--
--   This is the formal skeleton of an exact-distance assertion: the lower bound is proved in
--   the kernel (or reduced through SAT and LRAT) and the upper bound is supplied by a concrete
--   low-weight logical operator.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L202-L209
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L202-L209

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.eq_minWeight_of_bounds {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n) {E : Vec n}
    (hker : E ∈ LinearMap.ker M₁.toLin') (hnot : E ∉ M₂.certificateRowSpace) (hw : hammingNorm E =
      d₀)
    (hlower : ∀ F, F ∈ LinearMap.ker M₁.toLin' → F ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm F) :
    minWeightKernelOutsideRowSpace M₁ M₂ = d₀ := by sorry
