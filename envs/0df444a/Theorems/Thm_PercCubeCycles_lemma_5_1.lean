-- Prove2me | Theorems.Thm_PercCubeCycles_lemma_5_1
-- name    : PercCubeCycles.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:35:53.995899+00:00
-- url     : https://prove2.me/theorems/09d0ded2-6028-4677-8daf-3de69f7dc6b8
-- title:
--   Lemma 5.1 — one round of joining: $r-|M^+|\le(100d^4\log n/s)\,r$
-- statement:
--   Let $n,d,s\ge1$ and $r\ge2$ be integers, $G$ an $n$-vertex graph, and $S_1,\dots,S_{2r}\subseteq V(G)$ pairwise disjoint sets of size $s$. Assume $|N_G(A)|\ge|A|/d^2$ for every $A\subseteq V(G)$ with $|A|\le2n/3$. Let $M$ be a perfect matching on $[2r]$, and let $\mathcal M^+$ be the set of matchings $M^+$ on $[2r]$ satisfying:
--
--   1. (I) $M^+$ is edge disjoint from $M$, and $([2r],M\cup M^+)$ is a Hamilton cycle or acyclic.
--   2. (II) There are vertex-disjoint paths $P_{xy}$, $xy\in M^+$, with $P_{xy}$ an $S_x$-$S_y$ path in $G$ of length at most $L=20d^2\log n-1$, all avoiding $S_z$ for every $z$ not matched by $M^+$.
--
--   Let $M^+\in\mathcal M^+$ be of maximum cardinality. If $([2r],M\cup M^+)$ is not a Hamilton cycle, then
--   $$r-|M^+|\le\frac{100d^4\log n}{s}\,r.$$
--   This bounds the terminal pairs left unjoined after one round.
--
--   Differences from the source:
--   - encoding: matchings on $[2r]$ and paths indexed by the edges $xy$ → graphs on `Fin (2 * r)`, and walks indexed by pairs $x<y$; reason: one path per edge
--   - reading: an $S_x$-$S_y$ path → a path with one endpoint in $S_x$ and the other in $S_y$; reason: interior vertices may lie in sets of matched indices, as (II) only excludes unmatched ones
-- source:
--   Anastos, Linear-length cycles in the supercritical percolated hypercube, STOC 2027 submission (sha256 14e6f0eeea86205c661b9ec5b7259d5e903f4bcfacef3946a425ea6e60e837ae), Lemma 5.1, p.14

import Mathlib
import Definitions.Def_PercCubeCycles_Joining

set_option autoImplicit false

namespace PercCubeCycles

/-- Lemma 5.1, p.14, Anastos, *Linear-length cycles in the supercritical percolated hypercube*, STOC 2027 submission (sha256 14e6f0ee…). Let `n, d, s ≥ 1` and `r ≥ 2`, `G` an `n`-vertex graph, and `S₁, …, S_{2r}` pairwise
disjoint sets of size `s`, with `|N_G(A)| ≥ |A|/d²` for every `A` with `|A| ≤ 2n/3` (7). Let `M` be a perfect
matching on `[2r]` and `M⁺` of maximum cardinality in the set `𝓜⁺` of matchings satisfying (I) and (II).
If `([2r], M ∪ M⁺)` is not a Hamilton cycle, then `r − |M⁺| ≤ (100d⁴ log n / s) r` (8). -/
theorem lemma_5_1 {V : Type*} [Fintype V] (d s r : ℕ) (hd : 1 ≤ d) (hs : 1 ≤ s) (hr : 2 ≤ r)
    (hn : 1 ≤ Fintype.card V) (G : SimpleGraph V) (S : Fin (2 * r) → Finset V)
    (hS : Pairwise fun x y => Disjoint (S x) (S y)) (hScard : ∀ x, (S x).card = s)
    (h7 : ∀ A : Finset V, 3 * A.card ≤ 2 * Fintype.card V → A.card ≤ d ^ 2 * (nbhd G A).card)
    (M Mp : SimpleGraph (Fin (2 * r))) (hM : IsPerfectMatchingGraph M)
    (hMp : IsJoiningMatching G S d M Mp)
    (hmax : ∀ Mq, IsJoiningMatching G S d M Mq → Mq.edgeSet.ncard ≤ Mp.edgeSet.ncard)
    (hHam : ¬ IsHamiltonCycleGraph (M ⊔ Mp)) :
    (r : ℝ) - Mp.edgeSet.ncard ≤ 100 * (d : ℝ) ^ 4 * Real.log (Fintype.card V) / s * r := by sorry

end PercCubeCycles
