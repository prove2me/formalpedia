-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_remark25
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.remark25
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:49:47.152402+00:00
-- url     : https://prove2.me/theorems/6397e91a-b13e-41b3-8adf-d3fa21cdf492
-- title:
--   Remark 25: physical incidence matrix as a restriction
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   Let $R_N$ be the incidence matrix on all diagrams at both levels. There are injective inclusions of row and column shapes, preserving each diagram, for which
--
--   $$R_N^{(d)}=(R_N)_{\mathcal Y_{N-1}^{(d)},\mathcal Y_N^{(d)}}.$$
--
--   This is a rectangular restriction and does not require a lexicographic upper-left block.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 14, Remark 25: physical incidence matrix as a restriction

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Remark 25: separate row and column restrictions of the full rectangular
incidence matrix, without any upper-left-corner assertion (PDF p.14). -/
theorem remark25 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ (rows : Partition d (N-1) ↪ Partition N (N-1))
      (cols : Partition d N ↪ Partition N N),
      (∀ alpha, (rows alpha).val = alpha.val) ∧ (∀ mu, (cols mu).val = mu.val) ∧
      incidence d N = (incidence N N).submatrix rows cols := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
