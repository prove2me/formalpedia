-- Prove2me | Theorems.Thm_UnderstandingML_kmeans_step_nonincreasing
-- name    : UnderstandingML.kmeans_step_nonincreasing
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:17:20.264988+00:00
-- url     : https://prove2.me/theorems/0315fd73-59e3-4394-8661-1344014784b9
-- title:
--   Lemma 22.1: an iteration of the k-means algorithm (reassign to nearest centroids, recompute centroids) does not increase the k-means objective
-- statement:
--   **Lemma 22.1.** Each iteration of the k-means algorithm does not increase the k-means objective function (as given in Equation (22.1)).
--
--   Formally: if $C^{(t-1)}$ and $C^{(t)}$ are partitions of the data $X \subseteq \mathbb{R}^n$ into $k$ clusters and $C^{(t)}$ assigns every point to a nearest centroid $\mu(C^{(t-1)}_i)$ (ties arbitrary), then $G(C^{(t)}) \le G(C^{(t-1)})$.
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §22.2.1 pp. 313-314, Lemma 22.1 with its proof

import Definitions.Def_UnderstandingML_Clustering

open MeasureTheory

namespace UnderstandingML

/-- **Lemma 22.1** (p. 313). Each iteration of the k-means algorithm does not increase the
k-means objective function (as given in Equation (22.1)): if `C⁽ᵗ⁾` assigns every point of `X`
to a nearest centroid of the previous partition `C⁽ᵗ⁻¹⁾`, then `G(C⁽ᵗ⁾) ≤ G(C⁽ᵗ⁻¹⁾)`. -/
theorem kmeans_step_nonincreasing {n k : ℕ} (S : Finset (Vec n)) (C C' : Fin k → Finset (Vec n))
    (hC : IsPartition S C) (hC' : IsPartition S C')
    (hnear : IsNearestAssignment (fun i ↦ centroid (C i)) C') :
    kmeansObjective C' ≤ kmeansObjective C := by sorry

end UnderstandingML
