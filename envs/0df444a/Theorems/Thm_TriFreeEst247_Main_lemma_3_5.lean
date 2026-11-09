-- Prove2me | Theorems.Thm_TriFreeEst247_Main_lemma_3_5
-- name    : TriFreeEst247.Main.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:16:37.852559+00:00
-- url     : https://prove2.me/theorems/7f608ad0-0be6-4e55-b729-259b515ed521
-- title:
--   Lemma 3.5: color blocks
-- statement:
--   Let $G$ have $n\ge3$ vertices, let $\lambda\ge0$, and color its vertices with $L\ge1$ colors. Write $B_c$ for monochromatic input edges, $G_c=G-B_c$, and $E_i$ for the color-sum blocks. Then
--
--   $$c\text{ balanced}\Longrightarrow |B_c|\le\frac{n^2}{2L}.$$
--
--   For every coloring, each triangle of $G_c$ has three distinct edge blocks. For every deletion set $D\subseteq E(G)$,
--
--   $$J_\lambda(D\cup B_c)\le J_\lambda(D)+e(B_c).$$
--
--   All three clauses are asserted, and only the first is conditional on balance.
--
--   Differences from the source:
--   - encoding: finite graphs and their vertex sets → simple graphs on Fin n, with unordered edges and triangles; reason: relabeling preserves every source instance and all normalized quantities
--   - generalization: L = ceil(2/η) from Section 3.2 → every integer L ≥ 1; reason: the argument uses only positive L and specializes to the exact source parameter
--   - encoding: block 1 + ((c(x)+c(y)) mod L) → Fin L modular color sum; reason: this renumbers each block without changing any edge membership
-- source:
--   Asaf Shapira, Nick Kushnir, Triangle-Freeness: Estimation Is as Easy as Testing, STOC 2027 submission #247 (October 2026), source.pdf SHA-256 c24a6ad41f5c2465027e143e0aa757c3288add8cceb703078b9c0c2e18a0c3ad, p.12, Lemma 3.5

import Mathlib
import Definitions.Def_TriFreeEst247_Main_BlockUpdates

open scoped ENNReal

namespace TriFreeEst247.Main

theorem lemma_3_5 {n L : ℕ} (hn : 3 ≤ n) (hL : 1 ≤ L)
    (G : Graph n) (lam : ℝ) (hlam : 0 ≤ lam) (c : Fin n → Fin L) :
    (balanced c → ((monochromatic G c).card : ℝ) ≤ (n : ℝ)^2 / (2 * (L : ℝ))) ∧
    (∀ x y z, (edgeGraph (coloredEdges G c)).Adj x y →
      (edgeGraph (coloredEdges G c)).Adj y z → (edgeGraph (coloredEdges G c)).Adj z x →
      blockIndex (c x) (c y) ≠ blockIndex (c y) (c z) ∧
      blockIndex (c y) (c z) ≠ blockIndex (c z) (c x) ∧
      blockIndex (c z) (c x) ≠ blockIndex (c x) (c y)) ∧
    (∀ D : EdgeSet n, D ⊆ edges G →
      score G lam (D ∪ monochromatic G c) ≤ score G lam D + edgeDensity (monochromatic G c))
    := by sorry

end TriFreeEst247.Main
