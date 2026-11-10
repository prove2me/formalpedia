-- Prove2me | Theorems.Thm_RandTreeUniv_lemma_3_2
-- name    : RandTreeUniv.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:18.35402+00:00
-- url     : https://prove2.me/theorems/fa292fda-3545-4ee1-9a55-e31ba0f84999
-- title:
--   Lemma 3.2 — two half-depth path systems give a linking system
-- statement:
--   Consider integers $n$, $k=k(n)\ge3$ and $m=m(n)$ with $n=(k+1)m$. Put
--
--   $$
--   n_1=\Big\lceil\frac{k+2}{2}\Big\rceil m,\qquad S_1=[n_1],\qquad S_2=[n]\setminus[n_1-m].
--   $$
--
--   Fix $m$-tuples of distinct vertices $\mathbf a\subseteq S_1\setminus S_2$, $\mathbf b\subseteq S_2\setminus S_1$, and let $\mathbf c$ list $S_1\cap S_2$. Let $G$ be an exchangeable random graph on $[n]$ such that
--
--   1. (S1) whp $G[S_1]$ contains an $(\mathbf a,\mathbf c;\lceil(k+2)/2\rceil-1)$-path system;
--   2. (S2) whp $G[S_2]$ contains a $(\mathbf c,\mathbf b;\lceil(k+1)/2\rceil-1)$-path system.
--
--   Then whp $G$ contains an $(\mathbf a,\mathbf b;k)$-linking system.
--
--   This reduces linking systems, which require a path system for each of the $m!$ matchings, to two path systems on overlapping halves of the vertex set; exchangeability transfers (S1) and (S2) to all relabellings of $\mathbf c$ at once.
--
--   Differences from the source:
--   - generalization: integers n, k = k(n), m = m(n) with n = (k + 1)m and whp as n → ∞ → sequences k j ≥ 3, m j indexed by j, with hypotheses and conclusion as limits in j; reason: the paper's families are the case where j runs through the admissible n; the Lean statement also covers sequences along which n does not tend to infinity
--   - encoding: vertex set [n] and the sets [n₁], [n] ∖ [n₁ − m] → Fin n with [x] = {v | v < x}; a ⊆ S₁ ∖ S₂ as v + m < n₁, b ⊆ S₂ ∖ S₁ as n₁ ≤ v; reason: 0-based relabelling, no subtraction
--   - encoding: c = S₁ ∩ S₂ (a tuple treated as a set) → an injective tuple c whose range is S₁ ∩ S₂, in any order; reason: the paper treats tuples as sets (§2.1)
--   - encoding: exchangeable random graph → probability mass function on graphs on Fin n invariant under every vertex permutation; reason: same law
--   - encoding: G is an (a, b; k)-linking system → G contains an (a, b; k)-linking system (spanning, since n = (k + 1)m); reason: the paper's own convention, Definition 1.1, p.4
-- source:
--   A. Cohen Antonir, L. Lichev, M. Zhukovskii, Universality in random graphs via optimal linking systems: trees and beyond, arXiv:2608.06358 (held revision, sha256 33e85b21…69a55921), Lemma 3.2, p.14 (PDF 15)

import Mathlib
import Definitions.Def_RandTreeUniv_IsExchangeableLaw
import Definitions.Def_RandTreeUniv_IsPathSystemIn
import Definitions.Def_RandTreeUniv_IsLinkingSystemIn

set_option autoImplicit false

open scoped Classical

namespace RandTreeUniv

/-- **Lemma 3.2** (Cohen Antonir, Lichev, Zhukovskii, *Universality in random graphs via optimal linking systems: trees and beyond*, arXiv:2608.06358 (held revision, sha256 33e85b21…), p.14 (PDF 15)). Consider integers `n`, `k = k(n) ≥ 3` and `m = m(n)` with
`n = (k + 1)m`. Denote `n₁ := ⌈(k + 2)/2⌉ · m`, and define `S₁ := [n₁]`, `S₂ := [n] \ [n₁ − m]`.
Fix disjoint `m`-tuples of vertices `a ⊆ S₁ \ S₂`, `b ⊆ S₂ \ S₁` and `c = S₁ ∩ S₂`. Let `G` be an
exchangeable random graph with vertex set `[n]` such that
(S1) whp `G[S₁]` contains an `(a, c; ⌈(k + 2)/2⌉ − 1)`-path system;
(S2) whp `G[S₂]` contains a `(c, b; ⌈(k + 1)/2⌉ − 1)`-path system.
Then, whp `G` is an `(a, b; k)`-linking system.

**Formalization Note** The asymptotics run along an index `j`: at index `j` the parameters are
`k j ≥ 3`, `m j`, `n = (k j + 1) * m j`, the vertex set is `Fin n` (0-based, so `[x]` becomes
`{v | v < x}`), the law is the exchangeable `μ j`, and the tuples are injective maps
`Fin (m j) → Fin n`. `a ⊆ S₁ \ S₂` is `v + m < n₁`, `b ⊆ S₂ \ S₁` is `n₁ ≤ v`, and `c` lists the
vertices of `S₁ ∩ S₂ = {v | n₁ ≤ v + m ∧ v < n₁}` in some order (any order). Ceilings are
`Nat.ceil` of the real quotients. "`G` is a linking system" is containment of a (spanning)
linking system (Definition 1.1). whp is `Tendsto … atTop (𝓝 1)` in `j`. -/
theorem lemma_3_2 (k m : ℕ → ℕ) (hk : ∀ j, 3 ≤ k j)
    (μ : ∀ j, SimpleGraph (Fin ((k j + 1) * m j)) → ℝ) (hμ : ∀ j, IsExchangeableLaw (μ j))
    (a b c : ∀ j, Fin (m j) → Fin ((k j + 1) * m j))
    (ha : ∀ j, Function.Injective (a j)) (hb : ∀ j, Function.Injective (b j))
    (hc : ∀ j, Function.Injective (c j))
    (haS : ∀ j i, (a j i : ℕ) + m j < ⌈((k j : ℝ) + 2) / 2⌉₊ * m j)
    (hbS : ∀ j i, ⌈((k j : ℝ) + 2) / 2⌉₊ * m j ≤ (b j i : ℕ))
    (hcS : ∀ j (v : Fin ((k j + 1) * m j)),
      (⌈((k j : ℝ) + 2) / 2⌉₊ * m j ≤ (v : ℕ) + m j ∧ (v : ℕ) < ⌈((k j : ℝ) + 2) / 2⌉₊ * m j) ↔
        v ∈ Set.range (c j))
    (hS1 : Filter.Tendsto (fun j => lawProb (μ j) (fun G =>
      IsPathSystemIn G {v | (v : ℕ) < ⌈((k j : ℝ) + 2) / 2⌉₊ * m j} (a j) (c j)
        (⌈((k j : ℝ) + 2) / 2⌉₊ - 1))) Filter.atTop (nhds 1))
    (hS2 : Filter.Tendsto (fun j => lawProb (μ j) (fun G =>
      IsPathSystemIn G {v | ⌈((k j : ℝ) + 2) / 2⌉₊ * m j ≤ (v : ℕ) + m j} (c j) (b j)
        (⌈((k j : ℝ) + 1) / 2⌉₊ - 1))) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun j => lawProb (μ j) (fun G => IsLinkingSystemIn G Set.univ (a j) (b j) (k j)))
      Filter.atTop (nhds 1) := by sorry

end RandTreeUniv
