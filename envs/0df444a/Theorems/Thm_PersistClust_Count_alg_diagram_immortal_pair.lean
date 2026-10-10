-- Prove2me | Theorems.Thm_PersistClust_Count_alg_diagram_immortal_pair
-- name    : PersistClust.Count.alg_diagram_immortal_pair
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T11:09:35.524377+00:00
-- url     : https://prove2.me/theorems/294b82cc-98d7-4f85-a9cd-98cdd8027ccb
-- title:
--   Rips diagram equals barcode: immortal (essential) slice
-- statement:
--   This is the **immortal (essential) slice** of the theorem that the analytic 0-dimensional persistence diagram of the upper-star Rips filtration coincides with its elder-rule barcode.
--
--   Let $n$ points be equipped with values $g_i$ and a symmetric distance matrix $Dm$; let $\delta$ be the Rips threshold and $\sigma$ a non-decreasing sort order of the values $g$ (so vertices are processed in decreasing $g$-order). The upper-star Rips filtration $\{R_\delta(L^\alpha)\}_\alpha$ (Eq. (3) of RR-6968) has analytic 0-th persistence diagram $\mathrm{ripsDiagram}(Dm,g,\delta)=\mathrm{mult}(\mathrm{ripsRank}(Dm,g,\delta))$, defined from the rank function $\mathrm{ripsRank}(s,t)=$ the number of connected components of the subgraph $R_\delta(L^t)$ that meet $L^s$. Its elder-rule barcode $\mathrm{ripsBarcode}(g,Dm,\delta,\sigma)$ is produced by the union-find sweep of Procedure 1 with merge threshold $\tau=+\infty$.
--
--   For every real birth level $b$, the multiplicity of the point $(b,-\infty)$ is the same on both sides:
--   $$\mathrm{mult}(\mathrm{ripsRank})(b,-\infty) \;=\; \mathrm{ripsBarcode}(g,Dm,\delta,\sigma)(b,-\infty).$$
--   Both count the connected components of the full Rips graph $R_\delta$ whose highest-$g$ vertex has value exactly $b$, i.e. the entries of the sweep that survive the whole process and yield one immortal bar each.
--
--   The statement holds for *every* real $b$: when $b$ is not among the vertex values, both sides are $0$.
-- source:
--   Chazal--Guibas--Oudot--Skraba, RR-6968 (2009), Procedure 1 (τ=+∞ elder-rule sweep) and Eq. (3), standard 'persistence diagram of a finite filtration equals its barcode', immortal slice

import Mathlib
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count

theorem alg_diagram_immortal_pair
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b : ℝ) :
    ripsDiagram Dm g δ ((b : EReal), ⊥) = ripsBarcode g Dm δ σ ((b : EReal), ⊥) := by sorry

end PersistClust.Count
