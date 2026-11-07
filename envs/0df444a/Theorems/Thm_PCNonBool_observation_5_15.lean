-- Prove2me | Theorems.Thm_PCNonBool_observation_5_15
-- name    : PCNonBool.observation_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:30:56.589982+00:00
-- url     : https://prove2.me/theorems/9845d2e7-02e6-4ab8-adfb-b89282a88926
-- title:
--   Observation 5.15 (corrected: $\nu < c$) — $|X| \le |W|/(c-\nu)$
-- statement:
--   **Observation 5.15.** Let $G=(U\sqcup V,E)$ be an $(s,\Delta,c)$-boundary expander, let $W\subseteq V$ have size at most $\Delta s$, and let $\nu<c$. If a set $X\subseteq U$ has size at most $s$ and $|\partial X\setminus W|\le\nu|X|$, then
--   $$|X|\ \le\ \frac{|W|}{c-\nu}.$$
--
--   It bounds the size of a set that expands poorly once a few holes $W$ are deleted, and is the counting step behind Proposition 5.12.
--
--   Differences from the source:
--   - correction: no condition on ν → ν < c; reason: K_{1,5} (U = {u}, V = {1,…,5}) is a (1, 5, 5)-boundary expander; with W = ∅, X = {u}, ν = 6: |∂X \ W| = 5 ≤ 6|X|, but |W|/(c − ν) = 0 < 1 = |X|; at ν = c the right side is undefined
-- source:
--   Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, On the Power of Polynomial Calculus over Non-Boolean Domains, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), Observation 5.15, p.32 (PDF p.35)

import Mathlib
import Definitions.Def_PCNonBool_BipGraph
import Definitions.Def_PCNonBool_boundaryOn
import Definitions.Def_PCNonBool_IsBoundaryExpander

namespace PCNonBool

/-- **Observation 5.15** (Conneryd–Ghannane–Nordström–Pang–Risse–Sokolov, *On the Power of Polynomial Calculus over Non-Boolean Domains*, STOC 2027 submission manuscript, November 3, 2026 (sha256 b59a1a76…048ed), p.32 (PDF p.35)), corrected. Let `G` be an `(s, Δ, c)`-boundary
expander, `W ⊆ V` with `|W| ≤ Δs`, and `ν < c`. If `X ⊆ U` has `|X| ≤ s` and `|∂X \ W| ≤ ν|X|`,
then `|X| ≤ |W| / (c - ν)`.

**Formalization Note** Without `ν < c` the claim fails: `K_{1,5}` is a `(1, 5, 5)`-boundary expander,
and `W = ∅`, `X = {u}`, `ν = 6` satisfy the hypotheses while `|W|/(c - ν) = 0 < 1`. The hypothesis
`|W| ≤ Δs` is printed in the source and kept, although the conclusion does not need it. -/
theorem observation_5_15 {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (G : BipGraph U V) (s Δ : ℕ) (c ν : ℝ) (hG : IsBoundaryExpander G s Δ c) (hν : ν < c)
    (W : Finset V) (hW : W.card ≤ Δ * s) (X : Finset U) (hX : X.card ≤ s)
    (hXW : ((boundaryOn G Finset.univ X \ W).card : ℝ) ≤ ν * X.card) :
    (X.card : ℝ) ≤ W.card / (c - ν) := by sorry

end PCNonBool
