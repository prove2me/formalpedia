-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition20
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition20
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:46:39.365501+00:00
-- url     : https://prove2.me/theorems/71c1ff7c-9ca9-46f8-a96d-65df45e91690
-- title:
--   Proposition 20: full row rank of R
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   The rows are linearly independent, and
--
--   $$\operatorname{rank}_{\mathbb R}R_N^{(d)}=|\mathcal Y_{N-1}^{(d)}|.$$
--
--   This is full row rank over a field, with no rank certificate assumed as input.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 13, Proposition 20: full row rank of R

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

/-- Proposition 20: full row rank over the real field, with independent rows
(PDF p.13). d>=2,N>=2 are retained. -/
theorem proposition20 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) :
    (incidence d N).rank = Fintype.card (Partition d (N-1)) ∧
    LinearIndependent ℝ (fun alpha : Partition d (N-1) => incidence d N alpha) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
