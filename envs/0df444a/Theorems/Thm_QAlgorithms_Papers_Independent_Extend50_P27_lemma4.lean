-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma4
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:37:29.617753+00:00
-- url     : https://prove2.me/theorems/6ac7c177-02dd-43d7-baf9-c522434ed112
-- title:
--   Lemma 4: teleportation matrix as Ind-Res multiplicities
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
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 8, Lemma 4: teleportation matrix as Ind-Res multiplicities

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

/-- Lemma 4 (PDF pp.8–9). The column label is mu; the printed repeated nu is
corrected as the proof requires. The diagonal counts all restricted constituents. -/
theorem lemma4 {K : ℕ} (nu mu : Partition (K+1) (K+1)) :
    fullMatrix (K+1) nu mu =
      (∑ alpha : Partition (K+1) K,
        restrictionMultiplicity alpha nu * inductionMultiplicity mu alpha : ℕ) ∧
    removableCount nu.val = ∑ alpha : Partition (K+1) K, restrictionMultiplicity alpha nu := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
