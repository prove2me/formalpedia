-- Prove2me | Theorems.Thm_ParallelHAC_lemma_19_large_size_phases
-- name    : ParallelHAC.lemma_19_large_size_phases
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:42.720077+00:00
-- url     : https://prove2.me/theorems/3c730610-88c0-4be2-913c-3b3c046e55fd
-- title:
--   Lemma 19 — $O(\log n)$ phases start with a large size increase
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $d$ be a well-behaved linkage on $P$ ($n=|P|$, triangle constant $c_\Delta\ge1$); fix a $c$-approximate HAC run ($c\ge1$) and a point $x_0\in P$, and let $J$ be the number of phases. Then the number of phases $j\in\{2,\dots,J\}$ that start because of a large size increase is at most
--   $$C\,(\log_2 n+1).$$
--
--   Each such phase multiplies the size of $x_0$'s cluster by at least $3/2$, and that size is between $1$ and $n$.
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: O(log n) → C(log₂ n + 1) with C chosen before the point type, the instance and the run; reason: pins the asymptotic notation; log₂ 0 = 0 in Lean, so the bound is ≥ C for every n
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 19, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_phaseEnd
import Definitions.Def_ParallelHAC_HACRun_StartsLargeMerge

namespace ParallelHAC

universe u

/-- **Lemma 19** (p.24): the number of phases that start because of a large size increase is at
most `O(log n)`. There is an absolute constant `C` such that for every well-behaved linkage, every
`c`-approximate HAC run and every `x₀ ∈ P`, at most `C (log₂ n + 1)` of the phases
`j = 2, …, J` start because of a large size increase.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 19, printed p.24 (PDF p.27).

**Formalization Note.** `O(log n)` is `C (log₂ n + 1)` with `C` absolute (chosen before every
parameter). -/
theorem lemma_19_large_size_phases :
    ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (κ a cΔ b c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ cΔ → 1 ≤ c → WellBehaved P k κ a cΔ b d →
    ∀ (R : HACRun P d c) (x₀ : V), x₀ ∈ P →
      (((Finset.Icc 2 (R.numPhases x₀ cΔ)).filter
          (R.StartsLargeSizeIncrease x₀ cΔ)).card : ℝ) ≤ C * (Real.logb 2 P.card + 1) := by sorry

end ParallelHAC
