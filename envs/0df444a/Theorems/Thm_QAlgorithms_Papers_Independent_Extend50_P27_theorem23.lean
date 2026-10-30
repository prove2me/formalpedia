-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_theorem23
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.theorem23
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:48:14.914454+00:00
-- url     : https://prove2.me/theorems/7dbe5496-5863-44c1-89ed-4ff9b8f5bc61
-- title:
--   Theorem 23: teleportation matrix is the column Gram matrix
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   For the teleportation matrix independently defined by removable corners and single-box moves,
--
--   $$G_N^{(d)}=M_N^{(d)}.$$
--
--   Thus the teleportation matrix is the column Gram matrix, as a theorem rather than a definition.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 14, Theorem 23: teleportation matrix is the column Gram matrix

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

/-- Theorem 23, equality of independently constructed matrices, Eq.(50) (PDF p.14). -/
theorem theorem23 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    columnGram d N = teleportMatrix d N := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
