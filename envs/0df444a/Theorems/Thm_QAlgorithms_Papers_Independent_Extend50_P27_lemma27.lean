-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma27
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma27
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:50:40.889286+00:00
-- url     : https://prove2.me/theorems/b547d8b3-37dd-4ef5-9151-fd11c0bc989e
-- title:
--   Lemma 27: unique excluded outgoing edge at the height boundary
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   For a row shape $\alpha\in\mathcal Y_{N-1}^{(d)}$, if $h(\alpha)<d$, every addable-box extension has height at most $d$. If $h(\alpha)=d$, there is exactly one excluded extension:
--
--   $$\#\{\mu\vdash N:\alpha\in\mu,\ h(\mu)>d\}=1.$$
--
--   Thus below the height boundary no outgoing edge is lost; on the boundary exactly one is lost.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 15, Lemma 27: unique excluded outgoing edge at the height boundary

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

/-- Lemma 27: exactly one omitted outgoing edge at height d; no omitted edges
below the boundary (PDF p.15). Excluded columns, not retained columns, are counted. -/
theorem lemma27 {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N) (alpha : Partition d (N-1)) :
    (alpha.val.colLen 0 < d →
      ∀ mu : Partition N N, Predecessor alpha.val mu.val → mu.val.colLen 0 ≤ d) ∧
    (alpha.val.colLen 0 = d →
      ∃! mu : Partition N N, Predecessor alpha.val mu.val ∧ d < mu.val.colLen 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
