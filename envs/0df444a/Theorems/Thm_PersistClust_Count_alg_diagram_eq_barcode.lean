-- Prove2me | Theorems.Thm_PersistClust_Count_alg_diagram_eq_barcode
-- name    : PersistClust.Count.alg_diagram_eq_barcode
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T08:59:20.355632+00:00
-- url     : https://prove2.me/theorems/4e6a21bf-8f47-4006-a11b-0718ada58f9b
-- title:
--   Persistence diagram of the upper-star Rips filtration equals its elder-rule barcode
-- statement:
--   Let $L=\{g_i\}$ be a finite point cloud with vertex values $g : \{0,\dots,n-1\}\to\mathbb R$, let $D_m$ be a symmetric distance matrix on the cloud and let $R_\delta$ be the corresponding Rips graph (two distinct points are adjacent when their distance is at most $\delta$). The upper-star Rips filtration $\mathcal R^g_\delta(L)=\{R_\delta(L^\alpha)\}_\alpha$ of Eq. (3) has a 0-th persistence diagram $D_0\mathcal R^g_\delta(L)$, defined analytically: the multiplicity of a point $(b,d)$ of the extended plane is obtained from the rank function of the filtration (the number of connected components of $R_\delta(L^t)$ meeting $L^s$, for $s\ge t$) by taking infima of rank differences over small $\varepsilon$-windows.
--
--   Run the standard elder-rule (Kruskal) sweep on the same filtration: process the points in decreasing order of $g$ (any sort order $\sigma$ of $g$); each new local maximum of the Rips graph starts a component (a birth at $g_r$); when vertex $i$ is processed, every neighbouring entry is merged into the entry of the highest root, and each absorbed root $r$ dies at level $g_i$, giving the off-diagonal point $(g_r, g_i)$ (pairs with $g_r=g_i$ of zero persistence lie on the diagonal and are dropped); entries surviving at the end give the immortal points $(g_r,-\infty)$.
--
--   The theorem states that these two multiplicity functions coincide pointwise:
--
--   $$D_0\mathcal R^g_\delta(L) = \text{ripsBarcode}(g, D_m, \delta, \sigma) \quad\text{for any sort order } \sigma \text{ of } g.$$
--
--   This is the classical fact that the persistence diagram of a finite tame filtration equals its barcode. It is the analytic core behind the counting claim of Theorem 4.8 of the source paper.
--
--   **Formalization Note.** `ripsDiagram Dm g δ = mult (ripsRank Dm g δ)` is defined in `Definitions.Def_PersistClust_Count_Rips`/`..._Diagram`; `ripsBarcode g Dm δ σ` is the combinatorial elder-rule pairing defined in `Definitions.Def_PersistClust_Count_AlgBarcode`, which must be imported. The hypothesis $h_{D_m}$ (symmetry) makes the Rips graph undirected; $\sigma$ may break ties among equal $g$-values arbitrarily.
-- source:
--   Chazal\u2013Guibas\u2013Oudot\u2013Skraba, Persistence-Based Clustering in Riemannian Manifolds, INRIA Research Report 6968 (2009), \u00a72.2 pp. 8\u20139 (Eq. (1), rank function and diagram of a tame filtration) and \u00a74.2 (Rips filtration Eq. (3)); the standard persistence-pairing theorem for finite filtrations.

import Mathlib
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count
theorem alg_diagram_eq_barcode
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) :
    ripsDiagram Dm g δ = ripsBarcode g Dm δ σ := by sorry
end PersistClust.Count
