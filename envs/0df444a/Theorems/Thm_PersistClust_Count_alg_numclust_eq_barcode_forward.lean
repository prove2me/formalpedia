-- Prove2me | Theorems.Thm_PersistClust_Count_alg_numclust_eq_barcode_forward
-- name    : PersistClust.Count.alg_numclust_eq_barcode_forward
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T11:23:49.79256+00:00
-- url     : https://prove2.me/theorems/23062213-a9d7-4977-a57e-a6095cde5248
-- title:
--   Procedure 1 outputs at most the tau-prominent barcode copies
-- statement:
--   Let $L=\{g_i\}$ be a finite point cloud with vertex values $g$, $D_m$ a symmetric non-negative distance matrix, $\delta\ge 0$ a scale for the Rips graph $R_\delta$, $\tau>0$ a prominence threshold, and $\sigma$ a sort order of $g$ (a permutation with $g(\sigma_0)\le\dots\le g(\sigma_{n-1})$).
--
--   Procedure 1 of the source paper processes the points in decreasing order of $g$ with a union-find structure rooted at local maxima of $g$ in $R_\delta$; with merge threshold $\tau$ it merges a neighbouring entry whose root $r$ satisfies $g_r - g_i < \tau$. It outputs the number `numClusters` of final entries whose root satisfies $g_r\ge\tau$.
--
--   Let $\text{ripsBarcode}(g,D_m,\delta,\sigma)$ be the elder-rule barcode of the same upper-star Rips filtration: the multiplicity function of persistence pairs $(g_r, g_i)$ (birth at a peak, death by merging into an older component) with immortal classes at $(g_r, -\infty)$. This lemma is the forward half of the equality
--   $$\operatorname{numClusters} = \#\{(b,d,k): k<\text{ripsBarcode}(b,d),\; d\le b-\tau,\; \tau\le b\};$$
--   namely
--   $$\operatorname{numClusters}(g,D_m,\delta,\tau,\sigma) \;\le\; \#\{(b,d,k): k<\text{ripsBarcode}(b,d),\; d\le b-\tau,\; \tau\le b\}.$$
--
--   The injection sends a surviving root $r$ to its recorded barcode point together with the rank of $r$ among the roots sharing that point. The per-root death map of the plain ($\tau=+\infty$) sweep records, for each root, the level at which its entry was absorbed (or $-\infty$ if it is immortal); the $\tau$-thresholded merge rules kill exactly the pairs of prominence below $\tau$, so each surviving root contributes a distinct barcode copy in the region $d\le b-\tau$, $\tau\le b$.
--
--   **Formalization Note.** `numClusters` is in `Definitions.Def_PersistClust_Count_Algorithm`; `ripsBarcode` and `IsSortOrder` in `Definitions.Def_PersistClust_Count_AlgBarcode` (and `..._Algorithm`). The region count is `Set.encard` of the copy set; the birth condition is the closed inequality $\tau\le b$ and the prominence condition the closed inequality $d\le b-\tau$.
-- source:
--   Chazal–Guibas–Oudot–Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), §3 (Procedure 1 with Procedure 2, pp. 17–18) and §4.2, proof of Theorem 4.8 (pp. 21–23): forward half of the equality alg_numclust_eq_barcode.

import Mathlib
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count
theorem alg_numclust_eq_barcode_forward
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      ≤ {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard := by sorry
end PersistClust.Count
