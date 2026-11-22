-- Prove2me | Theorems.Thm_QECCertificates_le_minWeight_of_lower
-- name    : QECCertificates.le_minWeight_of_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:46:01.024245+00:00
-- url     : https://prove2.me/theorems/0582442a-0b71-4119-bf91-83866c583c2b
-- title:
--   QECCertificates: le min Weight of lower
-- statement:
--   **The lower-bound theorem**: if every undetectable nontrivial operator has weight at
--   least `d₀`, then the code distance is at least `d₀`.
--
--   The lower-bound side admits no short certificate unless there is a structural argument,
--   which is why LeanQEC reduces to SAT and UNSAT; this theorem provides the common interface
--   at which a lower-bound result and an upper-bound witness meet. For a computable
--   certificate on the lower-bound side see `QECCertificates.GF2.LowerBound`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L177-L194
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Witness.lean#L177-L194

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
public import Definitions.Def_LeanPool_QECCertificates_GF2_Witness
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
variable {n : ℕ}

theorem QECCertificates.le_minWeight_of_lower {m₁ m₂ : ℕ}
    (M₁ : Matrix (Fin m₁) (Fin n) (ZMod 2)) (M₂ : Matrix (Fin m₂) (Fin n) (ZMod 2)) {d₀ : ℕ}
    (hd : d₀ ≤ n)
    (h : ∀ E, E ∈ LinearMap.ker M₁.toLin' → E ∉ M₂.certificateRowSpace → d₀ ≤ hammingNorm E) :
    d₀ ≤ minWeightKernelOutsideRowSpace M₁ M₂ := by sorry
