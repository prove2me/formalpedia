-- Prove2me | Theorems.Thm_PersistClust_Count_alg_numclust_eq_barcode
-- name    : PersistClust.Count.alg_numclust_eq_barcode
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T09:01:01.466094+00:00
-- url     : https://prove2.me/theorems/5e1f3a91-c71e-416a-add4-42974478180e
-- title:
--   Procedure 1 with threshold τ outputs exactly the τ-prominent barcode pairs
-- statement:
--   Let $L=\{g_i\}$ be a finite point cloud with vertex values $g$, let $D_m$ be a symmetric non-negative distance matrix, $\delta\ge 0$ a scale for the Rips graph $R_\delta$, $\tau>0$ a prominence threshold, and $\sigma$ a sort order of $g$ (a permutation with $g(\sigma_0)\le\dots\le g(\sigma_{n-1})$).
--
--   Procedure 1 of the source paper processes the points in decreasing order of $g$ with a union-find structure whose entries are trees rooted at local maxima of $g$ in $R_\delta$. While vertex $i$ is processed: if no processed Rips-neighbour exists, $i$ starts a new entry (a peak); otherwise $i$ joins the entry of its highest processed neighbour, every neighbouring entry whose root $r$ satisfies $g_r - g_i < \tau$ (prominence less than $\tau$ at the current level) is merged into it, and finally the whole entry is merged into the neighbouring entry with the highest root whenever its own root is not $\tau$-prominent. The algorithm outputs the number `numClusters` of final entries whose root satisfies $g_r\ge\tau$.
--
--   Let $\text{ripsBarcode}(g,D_m,\delta,\sigma)$ be the elder-rule barcode of the same filtration: the multiplicity function of the persistence pairs $(g_r, g_i)$ (birth at a peak, death by merging into an older component) with the immortal classes at $(g_r, -\infty)$. The theorem states that the algorithm outputs exactly the number of barcode points of prominence at least $\tau$ born above level $\tau$:
--
--   $$\operatorname{numClusters}(g, D_m, \delta, \tau, \sigma) \;=\; \#\{\,(b,d,k)\;:\; k < \text{ripsBarcode}(b,d),\;\; d\le b-\tau,\;\; \tau\le b\,\}.$$
--
--   Immortal points $(b,-\infty)$ always have infinite prominence and contribute exactly when $b\ge\tau$. This is the combinatorial correctness of the $\tau$-thresholded merges: they kill exactly the non-$\tau$-prominent pairs, which is the step of the proof of Theorem 4.8 where the paper states that the algorithm discards the part $D_1^R$ of the Rips diagram and keeps the part $D_2^R$ located in $\Delta^S_\tau\cap\Lambda^E_\tau$.
--
--   **Formalization Note.** `numClusters` is defined in `Definitions.Def_PersistClust_Count_Algorithm`; `ripsBarcode g Dm δ σ` in `Definitions.Def_PersistClust_Count_AlgBarcode` (which must be imported). The region count is the cardinality of the set of copies $(b,d,k)$ with $k$ below the barcode multiplicity; the birth condition is the closed inequality $\tau\le b$.
-- source:
--   Chazal\u2013Guibas\u2013Oudot\u2013Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), \u00a73 (Procedure 1 with Procedure 2, pp. 17\u201318) and \u00a74.2, proof of Theorem 4.8 (pp. 21\u201323): the algorithm discards $D_1^R$ and keeps only $D_2^R\subset\Delta^S_\tau\cap\Lambda^E_\tau$.

import Mathlib
import Definitions.Def_PersistClust_Count_Algorithm
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count
theorem alg_numclust_eq_barcode
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (hDm0 : ∀ i j, 0 ≤ Dm i j)
    (δ τ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (σ : Fin n ≃ Fin n) (hσ : IsSortOrder g σ) :
    (numClusters g Dm δ τ σ : ℕ∞)
      = {q : (EReal × EReal) × ℕ | (q.2 : ℕ∞) < ripsBarcode g Dm δ σ q.1 ∧
          q.1.2 ≤ q.1.1 - (τ : EReal) ∧ (τ : EReal) ≤ q.1.1}.encard := by sorry
end PersistClust.Count
