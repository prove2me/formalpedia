-- Prove2me | Theorems.Thm_ThreshRankBIS_eq_7
-- name    : ThreshRankBIS.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:08:44.540815+00:00
-- url     : https://prove2.me/theorems/6d3d57f9-619f-402e-999d-9620d06eb55c
-- title:
--   Display (7) — every closed $A$ has $C\in\mathcal C$ with $|S_A\triangle C|\le\kappa(t(A)+1)$
-- statement:
--   Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, let $0<\rho<1$, and let $\mathcal C$ be a family of vertex sets with Lemma 6's success property: every $S\subseteq V(G)$ has a representative $C\in\mathcal C$ with $|S\triangle C|\le16(\mathrm{dist}(\mathbf 1_S,U)^2+1)$. Then, with $\kappa=\lceil256/\rho\rceil$,
--
--   $$
--   \text{every closed }A\text{ has some }C\in\mathcal C\text{ with }|S_A\triangle C|\le\kappa\,(t(A)+1). \tag{7}
--   $$
--
--   Display (7) is the form in which the spectral step is used: it is the hypothesis of the recovery step and of every container bound in Section 4.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
--   - encoding: the list on its simultaneous success event → a family 𝒞 satisfying Lemma 6's success property (hypothesis SpectralCover ρ E d 𝒞); reason: the success event is exactly the event that the list has this property; nothing else about the list is used
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), display (7), p.10; Lemma 6, p.9

import Mathlib
import Definitions.Def_ThreshRankBIS_SatisfiesEq7
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Display (7)**, p.10. On the simultaneous success event of the list `𝒞` of approximate cuts
of Lemma 6 (every `S ⊆ V(G)` has `C ∈ 𝒞` with `|S △ C| ≤ 16(dist(1_S, U)² + 1)`), every closed
`A ⊆ X` has some `C ∈ 𝒞` with `|S_A △ C| ≤ κ(t(A) + 1)`, `κ = ⌈256/ρ⌉`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), p.10, display (7);
the success property is the last sentence of Lemma 6, p.9.

**Formalization Note.** "The list on its simultaneous success event" is a family `𝒞` with the
success property `SpectralCover`, for `U` the spectral subspace of `L_G` for eigenvalues `≤ ρd`. -/
theorem eq_7 {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (𝒞 : Finset (Finset (V n)))
    (h𝒞 : SpectralCover ρ E d 𝒞) : SatisfiesEq7 ρ E 𝒞 := by sorry

end ThreshRankBIS
