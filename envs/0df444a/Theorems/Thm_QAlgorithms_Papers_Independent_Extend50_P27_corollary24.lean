-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_corollary24
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.corollary24
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:48:58.328992+00:00
-- url     : https://prove2.me/theorems/bb4e7a62-d4a5-4fb8-ac3e-f9f8dd3c6591
-- title:
--   Corollary 24: physical matrix PSD from Gram identity
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   The physical teleportation matrix is positive semidefinite:
--
--   $$M_N^{(d)}\succeq0.$$
--
--   This separately numbered consequence is retained even though Remark 11 already asserts positivity.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 14, Corollary 24: physical matrix PSD from Gram identity

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

/-- Corollary 24, separately retained although Remark 11 gives the same PSD claim
(PDF p.14). -/
theorem corollary24 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (teleportMatrix d N).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
