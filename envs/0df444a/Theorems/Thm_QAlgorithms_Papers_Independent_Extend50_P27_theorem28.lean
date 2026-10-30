-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_theorem28
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.theorem28
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:51:38.310822+00:00
-- url     : https://prove2.me/theorems/46f7e468-261f-41bf-ab27-f2296ae3650a
-- title:
--   Theorem 28: corrected row-Gram recursion
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   Let $D_{\alpha\alpha}=1$ when $h(\alpha)<d$ and $0$ when $h(\alpha)=d$, with off-diagonal entries zero. Then
--
--   $$H_N^{(d)}=D+M_{N-1}^{(d)}.$$
--
--   For $d=2$, the correction has rank one. For $d=N$, every row is below the boundary and $H_N^{(N)}=I+M_{N-1}^{(N)}$, the latter matrix being the full predecessor-level teleportation matrix up to the shape-preserving indexing.
--
--   This corrects Eq. (54)'s printed boundary condition while retaining both specializations of Eq. (55).
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 15, Theorem 28: corrected row-Gram recursion

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

/-- Theorem 28, Eqs.(53)–(55), corrected on the basis of Lemma 27 and Eq.(55)
(PDF p.15). Printed Eq.(54) says height=d; the correction is height<d. At N=d=2,
R=[1,1], H=[2], M_F(1)=[1], so the correction is [1]. -/
theorem theorem28 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    rowGram d N = heightCorrection d N + teleportMatrix d (N-1) ∧
    (heightCorrection 2 N).rank = 1 ∧
    rowGram 2 N = heightCorrection 2 N + teleportMatrix 2 (N-1) ∧
    rowGram N N = 1 + teleportMatrix N (N-1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
