-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma5
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma5
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:38:16.584983+00:00
-- url     : https://prove2.me/theorems/287a0431-cb1a-4cbb-9a00-82d0784d14a3
-- title:
--   Lemma 5: teleportation matrix as Ind-Res multiplicities
-- statement:
--   Let $N\ge1$. The full teleportation matrix $M_N$ is indexed by all $N$-box Young diagrams, with removable-corner counts on the diagonal and one on distinct single-box-move pairs. For $d\ge1$, $M_N^{(d)}$ is its principal restriction to shapes of height at most $d$, retaining the same diagonal counts.
--
--   For a Young diagram $\mu$, let $S^\mu$ be its complex Specht module, constructed as a Young left ideal, and $d_\mu=\dim S^\mu$. Restriction from $S_N$ to $S_{N-1}$ uses the subgroup fixing the last letter; induction uses this subgroup. Occurrence and multiplicity refer to actual modules, equivalently to dimensions of their intertwiner spaces.
--
--   For any row $
--   u$ and column $\mu$,
--
--   $$
--   (M_N)_{
--   u\mu}=\sum_{\alpha\vdash N-1}[\operatorname{Res}S^
--   u:S^\alpha]\,[\operatorname{Ind}S^\alpha:S^\mu],\qquad
--   n_
--   u=\sum_{\alpha\vdash N-1}[\operatorname{Res}S^
--   u:S^\alpha].
--   $$
--
--   Brackets denote actual representation multiplicity, and $n_
--   u$ is the removable-corner count. This identifies the entire matrix with restriction followed by induction.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 9, Lemma 5: teleportation matrix as Ind-Res multiplicities

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

/-- Lemma 5 (PDF p.9), a duplicate of Lemma 4 retained under its separate source
label. The varying column irrep is mu, as in the proof. -/
theorem lemma5 {K : ℕ} (nu mu : Partition (K+1) (K+1)) :
    fullMatrix (K+1) nu mu =
      (∑ alpha : Partition (K+1) K,
        restrictionMultiplicity alpha nu * inductionMultiplicity mu alpha : ℕ) ∧
    removableCount nu.val = ∑ alpha : Partition (K+1) K, restrictionMultiplicity alpha nu := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
