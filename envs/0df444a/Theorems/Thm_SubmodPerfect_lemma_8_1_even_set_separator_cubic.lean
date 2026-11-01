-- Prove2me | Theorems.Thm_SubmodPerfect_lemma_8_1_even_set_separator_cubic
-- name    : SubmodPerfect.lemma_8_1_even_set_separator_cubic
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T07:51:24.646993+00:00
-- url     : https://prove2.me/theorems/2e028ebd-dc23-4cef-839c-9b6fd2bf024c
-- title:
--   Lemma 8.1 — a $(w,\delta^2+2,c,\delta+1)$-even set separator, found in $O(n^3)$ time
-- statement:
--   Let $c\in[\tfrac12,1)$ and let $\delta\ge1$, $d\ge\delta+3$ be integers.
--
--   1. Every connected paw-friendly graph $G$ on $n$ vertices with all degrees at most $\delta$, together with every weight function $w:V(G)\to[0,1]$ with $w(G)=1$ such that $G$ has no $d$-bounded $(w,c)$-balanced separator, has a $(w,\delta^2+2,c,\delta+1)$-even set separator.
--   2. There are a program of the unit-cost RAM and a constant $C$ (depending on $c,d,\delta$ only) such that for all such $G$ and $w$, the program on input $(n,G,w,c)$ halts within $C\,(n+1)^3$ steps and outputs a $(w,\delta^2+2,c,\delta+1)$-even set separator of $G$.
--
--   In the paper the separator is $(X_1,X_2,L_1,\dots,L_{\delta^2})$, and Theorem 1.3 combines this lemma with the bounded-separator case.
--
--   **Formalization Note** Graphs are on $\{0,\dots,n-1\}$; machine, input layout and output decoder are those of `SubmodPerfect.Tame`. The weights are arbitrary, not only uniform.
--
--   Differences from the source:
--   - generalization: G has maximum degree δ → every vertex of G has degree at most δ (δ ≥ 1); reason: the source's statement is the case where δ is the maximum degree; for a graph of maximum degree δ′ ≤ δ the hypotheses on d and the conclusion only weaken with δ, so the source's statement at δ′ implies the Lean one
--   - encoding: constructed in O(|V(G)|^m) time → one program of the published unit-cost RAM (WilliamsonShmoys) and one constant C such that on input (n, adjacency matrix, w, c) the run halts within C·(n+1)^m steps with the separator in the output cells; graphs on Fin n; reason: the RAM has no real constants besides 0, so the threshold c is an input real cell; (n+1)^m avoids the degenerate n = 0
--   - reading: In particular, G is (δ² + 2, c, δ + 1, 3)-tame → no separate conjunct: it is the main clause applied to uniform weight functions w that satisfy the hypotheses; reason: the hypothesis (no d-bounded (w, c)-balanced separator) concerns one w, so the literal 'for every uniform w' does not follow from the lemma; the proof of Theorem 1.3 uses only the main clause
--   - encoding: one can find an even set representation of L → the program outputs the tuple L itself; reason: the representation is the tuple (X1, X2, L1, …, L_{δ²})
-- source:
--   Abrishami, Chudnovsky, Dibek, Vušković, Submodular functions and perfect graphs, arXiv:2110.00108v2 [math.CO] (preprint, 7 Jan 2024), https://arxiv.org/abs/2110.00108v2, Lemma 8.1, p.26

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_SubmodPerfect_Graphs
import Definitions.Def_SubmodPerfect_Wheels
import Definitions.Def_SubmodPerfect_Tame

set_option autoImplicit false
open Classical

namespace SubmodPerfect

/-- Abrishami, Chudnovsky, Dibek, Vušković, *Submodular functions and perfect graphs*, arXiv:2110.00108v2, Lemma 8.1, p.26.

Let `c ∈ [1/2, 1)` and `d, δ` positive integers with `d ≥ δ + 3`. Let `G` be a connected
paw-friendly graph on `n` vertices with maximum degree `δ`, `w : V(G) → [0, 1]` with `w(G) = 1`,
and suppose `G` has no `d`-bounded `(w, c)`-balanced separator. Then `G` has a
`(w, δ² + 2, c, δ + 1)`-even set separator `L`, and one can find (an even set representation of)
`L` in time `O(n³)`.

**Formalization Note.** Graphs are on `Fin n`. The second conjunct is the `O(n³)` construction:
one RAM program and one constant `C` (chosen after `c, d, δ`) such that, on input `(n, G, w, c)`
in the layout `sepInput`, the run halts within `C · (n + 1)³` steps and its output `sepOutput`
is such a separator. The weights `w` are arbitrary (not only uniform). -/
theorem lemma_8_1_even_set_separator_cubic (c : ℝ) (hc : 1 / 2 ≤ c ∧ c < 1) (d δ : ℕ)
    (hδ : 1 ≤ δ) (hdδ : δ + 3 ≤ d) :
    (∀ n (G : SimpleGraph (Fin n)) (w : Fin n → ℝ), G.Connected → IsPawFriendly G →
      MaxDegreeLe G δ → IsWeightFunctionOn w Finset.univ → wsum w Finset.univ = 1 →
      ¬ HasBoundedBalancedSepIn G Finset.univ w c d →
      ∃ L : Fin (δ ^ 2 + 2) → Finset (Fin n), IsEvenSetSeparator G w (δ ^ 2 + 2) c (δ + 1) L) ∧
    ∃ (program : List WilliamsonShmoys.PlanarRAMInstruction) (C : ℕ),
      ∀ n (G : SimpleGraph (Fin n)) (w : Fin n → ℝ), G.Connected → IsPawFriendly G →
        MaxDegreeLe G δ → IsWeightFunctionOn w Finset.univ → wsum w Finset.univ = 1 →
        ¬ HasBoundedBalancedSepIn G Finset.univ w c d →
        ∃ t ≤ C * (n + 1) ^ 3,
          RAMHalted program (WilliamsonShmoys.planarRAMRun program (sepInput n G w c) t) ∧
            IsEvenSetSeparator G w (δ ^ 2 + 2) c (δ + 1)
              (sepOutput n (δ ^ 2 + 2)
                (WilliamsonShmoys.planarRAMRun program (sepInput n G w c) t)) := by sorry

end SubmodPerfect
