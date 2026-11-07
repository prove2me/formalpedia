-- Prove2me | Theorems.Thm_SparseDisc_theorem_1_9
-- name    : SparseDisc.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:53:53.830972+00:00
-- url     : https://prove2.me/theorems/c08f93db-161f-4b9a-a938-496d4045e8f5
-- title:
--   Theorem 1.9 — 2-sparse discrepancy at most $\max(2,d)$ for degeneracy $d$ and $p(H)+1$ for pseudoarboricity $p$
-- statement:
--   Let $F = (f_v)_{v \in V}$ be a 2-sparse family of 1-Lipschitz set functions on a finite set of items, let $H = H(F)$ be its pattern (the simple graph underlying the item multigraph), $d = \operatorname{dgn}(H)$ its degeneracy, $p(H) = \max_{H'} \lceil |E(H')|/|V(H')| \rceil$ its pseudoarboricity and $n = |V|$. Then, whatever the vertex degrees, bundle sizes and private items,
--   $$
--   \operatorname{disc}(F) \le \max(2, d) \ \ (d \ge 1), \qquad \operatorname{disc}(F) \le 1 \ \ (d = 0), \qquad \operatorname{disc}(F) \le p(H) + 1 .
--   $$
--   The first two bounds are tight for $d \le 2$. Moreover:
--
--   1. **(a)** planar patterns have $\operatorname{disc}(F) \le 3$; patterns of treewidth $k$ have $\operatorname{disc}(F) \le \max(2, k)$; and $K_r$-minor-free patterns have $\operatorname{disc}(F) = O(r \sqrt{\log r})$.
--   2. **(b)** 2-degenerate patterns, among them cycles, cacti, outerplanar and series–parallel patterns, planar patterns of girth at least 6, and patterns obtained by subdividing every edge, as well as wheels, have $\operatorname{disc}(F) \le 2$, which is tight; subgraphs of $K_{q,n}$ have $\operatorname{disc}(F) \le \max(2, q)$.
--   3. **(c)** If every block of $H$ has maximum degree at most $\Delta \ge 2$, in particular if every function has at most $\Delta$ distinct neighbours, then $\operatorname{disc}(F) \le \lceil \Delta/2 \rceil + 1$; if the functions with more than $\Delta$ distinct neighbours form an independent set, then $\operatorname{disc}(F) \le \max(2, \Delta)$.
--   4. **(d)** If $n \ge 3$ then $\operatorname{disc}(F) \le \lceil n/2 \rceil$, and if $n \ge 4$ then $\operatorname{disc}(F) \le \lfloor n/2 \rfloor$.
--
--   Tightness is stated per pattern: every pattern with at least one edge carries, for every $\varepsilon > 0$, a 2-sparse 1-Lipschitz family with exactly that pattern and discrepancy greater than $2 - \varepsilon$; and every nonempty edgeless pattern carries a family of discrepancy at least $1$. The $O(r\sqrt{\log r})$ bound means: there is an absolute constant $C > 0$ with $\operatorname{disc}(F) \le C r \sqrt{\log r}$ for every $r \ge 1$ and every 2-sparse 1-Lipschitz family with $K_r$-minor-free pattern.
--
--   This is the paper's main result: for $t = 2$, the non-additive analogue of the Beck–Fiala question has a bound that depends only on the sparsity structure of the pattern, not on the number of functions, the number of items, or the sizes of the bundles.
--
--   **Formalization Note** Families are maps $f : V \to (\text{Finset } \iota \to \mathbb R)$ on finite types; "$\operatorname{disc}(F) \le c$" is the existence of a colouring achieving imbalance at most $c$ for every function. Planarity, minors and treewidth are the published `RobertsonSeymour1986.GM5` notions; outerplanarity and fans are `TaitTobin.Outerplanar`; series–parallel graphs are `ChvatalPolytopes.SeriesParallel.IsSeriesParallel`; girth is Mathlib's `egirth`. $\lceil x/2 \rceil$ and $\lfloor x/2 \rfloor$ are the natural numbers $(x+1)/2$ and $x/2$, and $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: families F = {f1, …, fn} on items [m] → f : V → Finset ι → ℝ with V and ι finite types; reason: Lean convention; same families
--   - generalization: 'the first two bounds are tight for d ≤ 2' → every pattern with an edge carries families of disc > 2 − ε for every ε > 0, and every nonempty edgeless pattern carries a family with disc ≥ 1 (¬ DiscLE f c for every c < 1); reason: the per-pattern form the proof gives (p.46, via Corollary 8.23(i)); it specializes to the printed claim by taking patterns of degeneracy 0, 1 and 2
--   - generalization: (b) '… have disc(F) ≤ 2, which is tight' → the same per-pattern tightness clause, for every pattern with an edge; reason: it specializes to tightness on each listed class by choosing a member with an edge
--   - reading: K_r-minor-free patterns have disc(F) = O(r√log r) → ∃ C > 0 such that for every r ≥ 1 and every such family disc(F) ≤ C r √(log r) (natural log); reason: the constant is absolute, chosen before r and the family; for r = 1 the pattern is empty and the bound 0 holds, so uniformity over all r ≥ 1 is the asymptotic statement
--   - reading: patterns of treewidth k → patterns of treewidth at most k (GM5.TreewidthLE); reason: the bound max(2, k) is monotone in k, so 'treewidth k' and 'treewidth at most k' give the same statement
--   - reading: series–parallel patterns → patterns with no subgraph homeomorphic to K₄ (ChvatalPolytopes.SeriesParallel.IsSeriesParallel); reason: the most general standard reading; it contains every series–parallel graph and its subgraphs
--   - generalization: patterns obtained by subdividing every edge → patterns isomorphic to a subdivision S_k(G₀) of a simple graph G₀ in which each edge is subdivided by one or more vertices; reason: the phrase is ambiguous between 'each edge once' and 'each edge at least once'; the Lean takes the more general reading, which specializes to the once-each reading at k ≡ 0 (such graphs stay 2-degenerate, with the subdivision vertices ordered first)
--   - reading: '2-degenerate patterns, among them cycles, cacti, outerplanar and series–parallel patterns, planar patterns of girth at least 6, and patterns obtained by subdividing every edge' → disc(F) ≤ 2 stated separately for 2-degenerate patterns and for each listed class; reason: the listed classes are named as covered by the bound; their 2-degeneracy is a proof step
--   - encoding: girth at least 6 → 6 ≤ egirth (⊤ for forests); reason: Lean convention; forests have infinite girth
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Theorem 1.9, pp.4–5

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_pattern
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_degeneracy
import Definitions.Def_SparseDisc_pseudoarboricity
import Definitions.Def_SparseDisc_IsCycle
import Definitions.Def_SparseDisc_IsCactus
import Definitions.Def_SparseDisc_IsSubdivision
import Definitions.Def_SparseDisc_IsWheel
import Definitions.Def_SparseDisc_IsSubgraphOfKqn
import Definitions.Def_SparseDisc_BlockDegreeLE
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE
import Definitions.Def_RobertsonSeymour1986_GM5_IsMinor

namespace SparseDisc

open Classical in
/-- **Theorem 1.9** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), pp.4–5). Let `F` be a 2-sparse family of
1-Lipschitz set functions, `H = H(F)` its pattern, `d = dgn(H)` and `p(H)` its pseudoarboricity.
Whatever the vertex degrees, bundle sizes and private items, `disc(F) ≤ max(2, d)` (`d ≥ 1`),
`disc(F) ≤ 1` (`d = 0`), `disc(F) ≤ p(H) + 1`. The first two bounds are tight for `d ≤ 2`.
Moreover: (a) planar patterns have `disc(F) ≤ 3`, patterns of treewidth `k` have
`disc(F) ≤ max(2, k)`, and `K_r`-minor-free patterns have `disc(F) = O(r√log r)`; (b) 2-degenerate
patterns, among them cycles, cacti, outerplanar and series–parallel patterns, planar patterns of
girth at least 6, and patterns obtained by subdividing every edge, as well as wheels, have
`disc(F) ≤ 2`, which is tight; subgraphs of `K_{q,n}` have `disc(F) ≤ max(2, q)`; (c) if every block
has maximum degree at most `Δ ≥ 2`, in particular if every function has at most `Δ` distinct
neighbours, then `disc(F) ≤ ⌈Δ/2⌉ + 1`; if the functions with more than `Δ` distinct neighbours form
an independent set, then `disc(F) ≤ max(2, Δ)`; (d) every 2-sparse family of `n ≥ 3` functions has
`disc(F) ≤ ⌈n/2⌉`, and `disc(F) ≤ ⌊n/2⌋` if `n ≥ 4`.

**Formalization Note** Families are `f : V → Finset ι → ℝ` with `V` (functions) and `ι` (items)
finite types; `H(F)` is `pattern f`; "`disc(F) ≤ c`" is `DiscLE f c`. Tightness is stated per
pattern, as the proof gives it (p.46, via Corollary 8.23(i)): every pattern with an edge carries a
family on items `Fin m` with discrepancy greater than `2 − ε` for every `ε > 0`, and every nonempty
edgeless pattern carries one with discrepancy at least `1`. `O(r√log r)` is an absolute constant
`C > 0` chosen before `r` and the family, with the natural logarithm. "Treewidth `k`" is treewidth
at most `k`; series–parallel is "no subgraph homeomorphic to `K₄`"; girth is `egirth` (`⊤` for
forests); "subdividing every edge" is subdividing each edge one or more times (covering the
once-each reading); the number of distinct
neighbours is the degree in `H`; `n = |V|`; `⌈x/2⌉`, `⌊x/2⌋` are `(x + 1) / 2`, `x / 2` in `ℕ`. -/
theorem theorem_1_9 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
        (f : V → Finset ι → ℝ), (∀ v, IsOneLipschitz (f v)) → IsTwoSparse f →
      (1 ≤ degeneracy (pattern f) → DiscLE f ((max 2 (degeneracy (pattern f)) : ℕ) : ℝ)) ∧
      (degeneracy (pattern f) = 0 → DiscLE f 1) ∧
      DiscLE f ((pseudoarboricity (pattern f) : ℝ) + 1) ∧
      (RobertsonSeymour1986.GM5.IsPlanar (pattern f) → DiscLE f 3) ∧
      (∀ k : ℕ, RobertsonSeymour1986.GM5.TreewidthLE (pattern f) k →
        DiscLE f ((max 2 k : ℕ) : ℝ)) ∧
      (HasDegenOrdering (pattern f) 2 → DiscLE f 2) ∧
      (IsCycle (pattern f) → DiscLE f 2) ∧
      (IsCactus (pattern f) → DiscLE f 2) ∧
      (TaitTobin.Outerplanar.IsOuterplanar (pattern f) → DiscLE f 2) ∧
      (ChvatalPolytopes.SeriesParallel.IsSeriesParallel (pattern f) → DiscLE f 2) ∧
      (RobertsonSeymour1986.GM5.IsPlanar (pattern f) ∧ 6 ≤ (pattern f).egirth → DiscLE f 2) ∧
      (IsSubdivision (pattern f) → DiscLE f 2) ∧
      (IsWheel (pattern f) → DiscLE f 2) ∧
      (∀ q : ℕ, IsSubgraphOfKqn (pattern f) q → DiscLE f ((max 2 q : ℕ) : ℝ)) ∧
      (∀ Δ : ℕ, 2 ≤ Δ → BlockDegreeLE (pattern f) Δ → DiscLE f ((((Δ + 1) / 2 : ℕ) : ℝ) + 1)) ∧
      (∀ Δ : ℕ, 2 ≤ Δ → (∀ v, (pattern f).degree v ≤ Δ) →
        DiscLE f ((((Δ + 1) / 2 : ℕ) : ℝ) + 1)) ∧
      (∀ Δ : ℕ, 2 ≤ Δ →
        (∀ u v, (pattern f).Adj u v → ¬ (Δ < (pattern f).degree u ∧ Δ < (pattern f).degree v)) →
        DiscLE f ((max 2 Δ : ℕ) : ℝ)) ∧
      (3 ≤ Fintype.card V → DiscLE f (((Fintype.card V + 1) / 2 : ℕ) : ℝ)) ∧
      (4 ≤ Fintype.card V → DiscLE f ((Fintype.card V / 2 : ℕ) : ℝ))) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (H₀ : SimpleGraph V), (∃ u v, H₀.Adj u v) →
      ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (f : V → Finset (Fin m) → ℝ),
        (∀ v, IsOneLipschitz (f v)) ∧ IsTwoSparse f ∧ pattern f = H₀ ∧ ¬ DiscLE f (2 - ε)) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V],
      ∃ (m : ℕ) (f : V → Finset (Fin m) → ℝ),
        (∀ v, IsOneLipschitz (f v)) ∧ IsTwoSparse f ∧ pattern f = ⊥ ∧
        ∀ c : ℝ, c < 1 → ¬ DiscLE f c) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r →
      ∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
        (f : V → Finset ι → ℝ), (∀ v, IsOneLipschitz (f v)) → IsTwoSparse f →
        ¬ RobertsonSeymour1986.GM5.IsMinor (⊤ : SimpleGraph (Fin r)) (pattern f) →
        DiscLE f (C * r * Real.sqrt (Real.log r))) := by sorry

end SparseDisc
