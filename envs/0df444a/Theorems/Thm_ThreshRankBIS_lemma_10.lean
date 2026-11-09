-- Prove2me | Theorems.Thm_ThreshRankBIS_lemma_10
-- name    : ThreshRankBIS.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:13:15.139239+00:00
-- url     : https://prove2.me/theorems/77ac92bc-deb3-4787-bcaf-383f2d25e1bc
-- title:
--   Lemma 10 — partial neighborhoods by greedy deletion, $|\mathcal F_t|\le K\sum_{j\le\lfloor2r/d\rfloor}\binom nj$
-- statement:
--   Let $G$ be a simple $d$-regular bipartite graph with $|X|=|Y|=n$, $d\ge1$, let $0<\rho<1$, $\kappa=\lceil256/\rho\rceil$, and let $\mathcal C$ be a list of approximate cuts satisfying (7), $K=|\mathcal C|$. For each integer $t\ge0$ put $r=\kappa(t+1)$. There is a family $\mathcal F_t\subseteq2^Y$ with
--
--   $$
--   |\mathcal F_t|\le K\sum_{j=0}^{\min\{n,\lfloor2r/d\rfloor\}}\binom nj \tag{12}
--   $$
--
--   such that every closed set $A$ of deficit $t$ has a partial neighborhood $F_0\in\mathcal F_t$ with $F_0\subseteq N(A)$ and $|N(A)\setminus F_0|\le2(t+r)$.
--
--   This is the first stage of the container encoding: a short description of most of the neighborhood of every closed set, built from the approximate cuts and a few vertex choices.
--
--   Differences from the source:
--   - encoding: a simple d-regular bipartite graph G = (X ∪ Y, E) with |X| = |Y| = n and d ≥ 1 → the graph HiddenPartition.bip E of a biadjacency matrix E : Fin n → Fin n → Bool with all row and column sums d (IsRegular E d), 1 ≤ d and 0 < n; reason: every such graph is exactly one such matrix after numbering each side by Fin n; such a graph has n ≥ d ≥ 1, and 0 < n only excludes the empty matrix, which is vacuously d-regular
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 10, p.12, display (12); standing hypothesis §4, p.12

import Mathlib
import Definitions.Def_ThreshRankBIS_SatisfiesEq7
set_option autoImplicit false
open Finset

namespace ThreshRankBIS

/-- **Lemma 10 (Partial neighborhoods by greedy deletion)**, p.12. Let `𝒞` be a list of
approximate cuts satisfying (7), `K = |𝒞|`. For each integer `t ≥ 0`, put `r = κ(t + 1)`. There
is a family `ℱ_t ⊆ 2^Y` with `|ℱ_t| ≤ K ∑_{j=0}^{min{n,⌊2r/d⌋}} binom(n, j)` (display (12)) such
that every closed set `A` of deficit `t` has a partial neighborhood `F_0 ∈ ℱ_t` with
`F_0 ⊆ N(A)` and `|N(A) ∖ F_0| ≤ 2(t + r)`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Lemma 10, p.12; the
standing hypothesis "Fix λ ≥ λ0 > 0 and a list of approximate cuts satisfying (7)", §4, p.12.

**Formalization Note.** Subsets of `Y` are `Finset (Fin n)`; `κ = ⌈256/ρ⌉`; `⌊2r/d⌋` is
natural-number division. The fugacity of §4's standing sentence plays no role here. -/
theorem lemma_10 {n d : ℕ} (E : Fin n → Fin n → Bool) (hreg : IsRegular E d)
    (hd : 1 ≤ d) (hn : 0 < n) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (𝒞 : Finset (Finset (V n)))
    (h7 : SatisfiesEq7 ρ E 𝒞) (t : ℕ) :
    ∃ Ft : Finset (Finset (Fin n)),
      #Ft ≤ #𝒞 * ∑ j ∈ range (min n (2 * (kappa ρ * (t + 1)) / d) + 1), n.choose j ∧
      ∀ A : Finset (Fin n), IsClosedLeft E A → deficit E A = t →
        ∃ F0 ∈ Ft, F0 ⊆ nbhd E A ∧ #(nbhd E A \ F0) ≤ 2 * (t + kappa ρ * (t + 1)) := by sorry

end ThreshRankBIS
