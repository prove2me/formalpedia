-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_incidence_properties
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.incidence_properties
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:45:41.299433+00:00
-- url     : https://prove2.me/theorems/a3c6278e-234c-40b0-b009-a849bb624984
-- title:
--   Definition 18, following properties 1-3: physical incidence matrix
-- statement:
--   Let $N,d\ge2$. Write $\mathcal Y_j^{(d)}$ for the $j$-box Young diagrams of height at most $d$. Define $R=R_N^{(d)}$ by $R_{\alpha\mu}=1$ when $\mu$ is obtained from $\alpha$ by adding one box, and zero otherwise. Its column and row Gram matrices are $G=R^{\mathsf T}R$ and $H=RR^{\mathsf T}$, over $\mathbb R$.
--
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   The row and column sums count actual physical constituents:
--
--   $$\sum_\mu R_{\alpha\mu}=\sum_\mu[\operatorname{Ind}S^\alpha:S^\mu],\qquad
--   \sum_\alpha R_{\alpha\mu}=\sum_\alpha[\operatorname{Res}S^\mu:S^\alpha].$$
--
--   Moreover $R_{\alpha\mu}=1$ if and only if the concrete physical projector $F_\mu(\alpha)$ of Eq. (145) is nonzero. These are all three properties following Definition 18.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 13, Definition 18, following properties 1-3: physical incidence matrix

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

/-- All three properties after Definition 18, including nonzero concrete physical
projectors, not merely adjacency redefined as occurrence (PDF p.13). -/
theorem incidence_properties {d K : ℕ} (hd : 0 < d) (hN : 1 ≤ K) :
    (∀ alpha : Partition d K,
      (∑ mu : Partition d (K+1), incidence d (K+1) alpha mu) =
        (∑ mu : Partition d (K+1), inductionMultiplicity mu alpha : ℕ)) ∧
    (∀ mu : Partition d (K+1),
      (∑ alpha : Partition d K, incidence d (K+1) alpha mu) =
        (∑ alpha : Partition d K, restrictionMultiplicity alpha mu : ℕ)) ∧
    (∀ (alpha : Partition d K) (mu : Partition d (K+1)),
      incidence d (K+1) alpha mu = 1 ↔ physicalProjector alpha mu ≠ 0) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
