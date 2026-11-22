-- Prove2me | Theorems.Thm_QECCertificates_exists_ne_zero_mulVec_eq_zero_of_rank_lt
-- name    : QECCertificates.exists_ne_zero_mulVec_eq_zero_of_rank_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:04:15.045556+00:00
-- url     : https://prove2.me/theorems/c861e75a-eb96-4ab3-be3c-09820e3ab2e6
-- title:
--   QECCertificates: exists ne zero mul Vec eq zero of rank lt
-- statement:
--   **Full rank fails $\Longrightarrow$ a nonzero kernel vector**: when
--   $M.\mathrm{rank}<n$ we have $\ker M\ne0$.
--
--   The construction is explicit: after row reduction there are fewer than $n$ pivot columns,
--   hence a **free column** $j$, and `kerVec` takes the value 1 on that column
--   (`exists_light_mem_kerL`); it is orthogonal to every row of $M$, so multiplying by $M$ on
--   the left gives zero.
--
--   **This is the bridge on the threshold side**: every factor of
--   $k=k_1k_2+k_1^\top k_2^\top$ is a $\dim\ker$, whereas what "the kernel is nontrivial"
--   requires is the **existence of a nonzero kernel vector**, not a dimension. The companion
--   paper argued this conversion only arithmetically; this theorem puts it into the kernel.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L243-L264
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/RankCertificate.lean#L243-L264

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_KernelBasis
public import Definitions.Def_LeanPool_QECCertificates_GF2_RankCertificate
set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open scoped BigOperators
open _root_.Matrix
variable {n : ℕ}

theorem QECCertificates.exists_ne_zero_mulVec_eq_zero_of_rank_lt {m n : ℕ} (M : Matrix (Fin m) (Fin n) (ZMod 2))
    (h : M.rank < n) : ∃ v : Vec n, M *ᵥ v = 0 ∧ v ≠ 0 := by sorry
