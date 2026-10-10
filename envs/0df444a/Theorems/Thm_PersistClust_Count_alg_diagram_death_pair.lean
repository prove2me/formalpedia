-- Prove2me | Theorems.Thm_PersistClust_Count_alg_diagram_death_pair
-- name    : PersistClust.Count.alg_diagram_death_pair
-- status  : Proved
-- author  : @fabianroll
-- created : 2026-10-09T11:10:09.277754+00:00
-- url     : https://prove2.me/theorems/ee075464-a0d9-4d97-8796-734a0b098847
-- title:
--   Rips diagram equals barcode: finite-persistence (death) slice
-- statement:
--   This is the **finite-persistence (death) slice** of the theorem that the analytic 0-dimensional persistence diagram of the upper-star Rips filtration coincides with its elder-rule barcode.
--
--   Under the same setup as the immortal slice — values $g_i$, symmetric $Dm$, Rips threshold $\delta$, decreasing sort order $\sigma$, upper-star Rips filtration $\{R_\delta(L^\alpha)\}_\alpha$ (Eq. (3) of RR-6968), analytic diagram $\mathrm{mult}(\mathrm{ripsRank})$, and elder-rule barcode $\mathrm{ripsBarcode}$ from Procedure 1 with $\tau=+\infty$ — for all real levels $d<b$ the multiplicity of the off-diagonal point $(b,d)$ agrees:
--   $$\mathrm{mult}(\mathrm{ripsRank})(b,d) \;=\; \mathrm{ripsBarcode}(g,Dm,\delta,\sigma)(b,d).$$
--   Both count the elder-rule merge events in which a component whose highest-$g$ vertex has value $b$ is absorbed at level $d$ into an older (higher-$g$) component — the persistence pairs with birth $b$ and death $d$.
--
--   The statement holds for *all* real $d<b$: when $b$ or $d$ is not a vertex value, both sides are $0$.
-- source:
--   Chazal--Guibas--Oudot--Skraba, RR-6968 (2009), Procedure 1 (τ=+∞ elder-rule sweep) and Eq. (3), standard 'persistence diagram of a finite filtration equals its barcode', finite-interval slice

import Mathlib
import Definitions.Def_PersistClust_Count_Rips
import Definitions.Def_PersistClust_Count_AlgBarcode

namespace PersistClust.Count

theorem alg_diagram_death_pair
    (n : ℕ) (g : Fin n → ℝ) (Dm : Fin n → Fin n → ℝ)
    (hDm : ∀ i j, Dm i j = Dm j i) (δ : ℝ) (σ : Fin n ≃ Fin n)
    (hσ : IsSortOrder g σ) (b d : ℝ) (hbd : d < b) :
    ripsDiagram Dm g δ ((b : EReal), (d : EReal)) =
      ripsBarcode g Dm δ σ ((b : EReal), (d : EReal)) := by sorry

end PersistClust.Count
