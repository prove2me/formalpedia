-- Prove2me | Theorems.Thm_SparseDisc_corollary_8_34
-- name    : SparseDisc.corollary_8_34
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:53:41.210459+00:00
-- url     : https://prove2.me/theorems/e7e0c0d6-cb5a-490b-8017-f70c690587ca
-- title:
--   Corollary 8.34 — bounds for 2-sparse families: 2-degenerate and wheels, planar, treewidth, block degree, $n$ functions
-- statement:
--   Let $F = (f_v)_{v \in V}$ be a 2-sparse family of 1-Lipschitz set functions on finitely many items, with arbitrary bundle sizes and private items, and let $H(F)$ be its pattern and $n = |V|$.
--
--   1. If $H(F)$ is 2-degenerate or a wheel, then $\operatorname{disc}(F) \le 2$, which is tight; this includes outerplanar and series–parallel patterns, planar patterns of girth at least 6, cacti, fans and $K_4$.
--   2. Planar patterns have $\operatorname{disc}(F) \le 3$, and patterns of treewidth $k$ have $\operatorname{disc}(F) \le \max(2, k)$.
--   3. If every block of $H(F)$ has maximum degree at most $\Delta \ge 2$, then $\operatorname{disc}(F) \le \lceil \Delta/2 \rceil + 1$; and if the functions with more than $\Delta$ distinct neighbours form an independent set, then $\operatorname{disc}(F) \le \max(2, \Delta)$.
--   4. If $n \ge 3$ then $\operatorname{disc}(F) \le \lceil n/2 \rceil$, and if $n \ge 4$ then $\operatorname{disc}(F) \le \lfloor n/2 \rfloor$.
--
--   Tightness in part 1 means: for every 2-degenerate or wheel pattern $H_0$ with at least one edge and every $\varepsilon > 0$ there is a 2-sparse family of 1-Lipschitz functions with pattern exactly $H_0$ and discrepancy greater than $2 - \varepsilon$.
--
--   **Formalization Note** Fans are the published `TaitTobin.Outerplanar.fan`; outerplanarity is `TaitTobin.Outerplanar.IsOuterplanar` (a plane drawing with every vertex on the closure of the outer face); treewidth is `RobertsonSeymour1986.GM5.TreewidthLE`; $\lceil x/2 \rceil$ and $\lfloor x/2 \rfloor$ are the natural numbers $(x+1)/2$ and $x/2$. The second bound of part 4 rests on the computer-assisted Theorem 3.8(b) in the paper's proof.
--
--   Differences from the source:
--   - encoding: families F = {f1, …, fn} on items [m] → f : V → Finset ι → ℝ with V and ι finite types; reason: Lean convention; same families
--   - generalization: disc(F) ≤ 2 for 2-degenerate or wheel patterns, 'which is tight' → for every 2-degenerate or wheel pattern H₀ with an edge and every ε > 0 there is a 2-sparse 1-Lipschitz family on items Fin m with pattern H₀ and disc > 2 − ε; reason: the per-pattern form the proof gives (Corollary 8.23(i), p.39); it specializes to the printed tightness on any member of the class with an edge
--   - reading: 'this includes outerplanar and series–parallel patterns, planar patterns of girth at least 6, cacti, fans and K4' → disc(F) ≤ 2 for each of these patterns; reason: the sentence names patterns covered by the bound; their membership in the 2-degenerate or wheel classes is a proof step
--   - reading: patterns of treewidth k → patterns of treewidth at most k (GM5.TreewidthLE); reason: the bound max(2, k) is monotone in k, so 'treewidth k' and 'treewidth at most k' give the same statement
--   - reading: series–parallel patterns → patterns with no subgraph homeomorphic to K₄ (ChvatalPolytopes.SeriesParallel.IsSeriesParallel); reason: the most general standard reading; it contains every series–parallel graph and its subgraphs
--   - encoding: girth at least 6 → 6 ≤ egirth (⊤ for forests); reason: Lean convention; forests have infinite girth
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions: Acyclic, Bounded-Degree and Degenerate Sparsity Patterns, STOC 2027 submission (manuscript sha256 0f09ec60…25b81), Corollary 8.34, p.44

import Mathlib
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_pattern
import Definitions.Def_SparseDisc_DiscLE
import Definitions.Def_SparseDisc_HasDegenOrdering
import Definitions.Def_SparseDisc_IsWheel
import Definitions.Def_SparseDisc_IsCactus
import Definitions.Def_SparseDisc_BlockDegreeLE
import Definitions.Def_TaitTobin_Outerplanar_Setting
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_RobertsonSeymour1986_GM5_IsPlanar
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

namespace SparseDisc

open Classical in
/-- **Corollary 8.34** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.44). For 2-sparse families of 1-Lipschitz
functions with arbitrary bundle sizes and private items: (i) if `H(F)` is 2-degenerate or a wheel,
then `disc(F) ≤ 2`, which is tight; this includes outerplanar and series–parallel patterns, planar
patterns of girth at least 6, cacti, fans and `K₄`; (ii) planar patterns have `disc(F) ≤ 3`, and
patterns of treewidth `k` have `disc(F) ≤ max(2, k)`; (iii) if every block of `H(F)` has maximum
degree at most `Δ ≥ 2`, then `disc(F) ≤ ⌈Δ/2⌉ + 1`, and if the functions with more than `Δ` distinct
neighbours form an independent set, then `disc(F) ≤ max(2, Δ)`; (iv) every 2-sparse family of
`n ≥ 3` functions has `disc(F) ≤ ⌈n/2⌉`, and `disc(F) ≤ ⌊n/2⌋` if `n ≥ 4`.

**Formalization Note** Families are `f : V → Finset ι → ℝ` on finite types, `H(F)` is `pattern f`.
"Tight" is stated per pattern: every 2-degenerate or wheel pattern with an edge carries a family
of discrepancy greater than `2 − ε` for every `ε > 0`. "Treewidth `k`" is treewidth at most `k`
(`GM5.TreewidthLE`); girth is Mathlib's `egirth` (`⊤` for forests); fans are the published
`TaitTobin.Outerplanar.fan`; outerplanarity and series–parallel graphs are the published
`TaitTobin.Outerplanar.IsOuterplanar` and `ChvatalPolytopes.SeriesParallel.IsSeriesParallel`
(no subgraph homeomorphic to `K₄`); `n` is `Fintype.card V`, and `⌈x/2⌉`, `⌊x/2⌋` are the natural
numbers `(x + 1) / 2`, `x / 2`. -/
theorem corollary_8_34 :
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
        (f : V → Finset ι → ℝ), (∀ v, IsOneLipschitz (f v)) → IsTwoSparse f →
      ((HasDegenOrdering (pattern f) 2 ∨ IsWheel (pattern f)) → DiscLE f 2) ∧
      (TaitTobin.Outerplanar.IsOuterplanar (pattern f) → DiscLE f 2) ∧
      (ChvatalPolytopes.SeriesParallel.IsSeriesParallel (pattern f) → DiscLE f 2) ∧
      (RobertsonSeymour1986.GM5.IsPlanar (pattern f) ∧ 6 ≤ (pattern f).egirth → DiscLE f 2) ∧
      (IsCactus (pattern f) → DiscLE f 2) ∧
      (∀ n : ℕ, Nonempty (pattern f ≃g TaitTobin.Outerplanar.fan n) → DiscLE f 2) ∧
      (Nonempty (pattern f ≃g (⊤ : SimpleGraph (Fin 4))) → DiscLE f 2) ∧
      (RobertsonSeymour1986.GM5.IsPlanar (pattern f) → DiscLE f 3) ∧
      (∀ k : ℕ, RobertsonSeymour1986.GM5.TreewidthLE (pattern f) k →
        DiscLE f ((max 2 k : ℕ) : ℝ)) ∧
      (∀ Δ : ℕ, 2 ≤ Δ → BlockDegreeLE (pattern f) Δ → DiscLE f ((((Δ + 1) / 2 : ℕ) : ℝ) + 1)) ∧
      (∀ Δ : ℕ, 2 ≤ Δ →
        (∀ u v, (pattern f).Adj u v → ¬ (Δ < (pattern f).degree u ∧ Δ < (pattern f).degree v)) →
        DiscLE f ((max 2 Δ : ℕ) : ℝ)) ∧
      (3 ≤ Fintype.card V → DiscLE f (((Fintype.card V + 1) / 2 : ℕ) : ℝ)) ∧
      (4 ≤ Fintype.card V → DiscLE f ((Fintype.card V / 2 : ℕ) : ℝ))) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (H₀ : SimpleGraph V),
      (HasDegenOrdering H₀ 2 ∨ IsWheel H₀) → (∃ u v, H₀.Adj u v) → ∀ ε : ℝ, 0 < ε →
      ∃ (m : ℕ) (f : V → Finset (Fin m) → ℝ), (∀ v, IsOneLipschitz (f v)) ∧ IsTwoSparse f ∧
        pattern f = H₀ ∧ ¬ DiscLE f (2 - ε)) := by sorry

end SparseDisc
