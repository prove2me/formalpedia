-- Prove2me | Theorems.Thm_SteinerNav_annuli_cover_targets
-- name    : SteinerNav.annuli_cover_targets
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:47:30.869751+00:00
-- url     : https://prove2.me/theorems/f45cb4d1-e332-48fa-b50c-bde28e8832aa
-- title:
--   §4.1, p.7 — the targets around a source lie in the $L$ dyadic annuli
-- statement:
--   Let $d\ge1$ and let $P\subset\mathbb R^d$ have $n\ge2$ points, minimum distance $\sigma$, aspect ratio $\Delta$, and $L=1+\lfloor\log_2\Delta\rfloor$. For every source $s\in P$ and every target $t\in P\setminus\{s\}$ there is an index $0\le i<L$ with
--   $$2^i\sigma\ \le\ \|s-t\|\ \le\ 2^{i+1}\sigma .$$
--
--   So the $L$ annuli with inner radii $2^i\sigma$ and outer radii $2^{i+1}\sigma$, $0\le i<L$, contain all of $P\setminus\{s\}$; this includes $\Delta=1$, where $L=1$.
--
--   Differences from the source:
--   - encoding: "the targets lie in the L annuli" (half-open annuli implicit) → closed annuli, an index i with both inequalities non-strict; reason: the page assigns a boundary target to one of its annuli, and the closed form says exactly that each target has at least one annulus.
-- source:
--   Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, Sparse α-Navigable Graphs in Euclidean Space via Steiner Points, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7 (paragraph before Corollary 4.2)

import Mathlib
import Definitions.Def_SteinerNav_aspectRatio

namespace SteinerNav

/-- For a source `s ∈ P`, every target of `P \ {s}` lies in one of the `L` annuli with inner radius
`2^i σ`, `0 ≤ i < L`, and outer radius `2^(i+1) σ`, where `L = 1 + ⌊log₂ Δ⌋`; this includes `Δ = 1`
(Conway, Dhulipala, Farach-Colton, Shechter, Suel, Wen, *Sparse α-Navigable Graphs in Euclidean Space via Steiner Points*, STOC 2027 submission (manuscript sha256 e396eee6…), §4.1, p.7). -/
theorem annuli_cover_targets {d : ℕ} (hd : 1 ≤ d) (P : Finset (Pt d)) (hn : 2 ≤ P.card)
    (s t : Pt d) (hs : s ∈ P) (ht : t ∈ P) (hts : t ≠ s) :
    ∃ i < annulusCount P,
      (2 : ℝ) ^ i * minDist P ≤ dist s t ∧ dist s t ≤ (2 : ℝ) ^ (i + 1) * minDist P := by sorry

end SteinerNav
