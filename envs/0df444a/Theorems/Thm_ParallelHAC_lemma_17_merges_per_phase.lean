-- Prove2me | Theorems.Thm_ParallelHAC_lemma_17_merges_per_phase
-- name    : ParallelHAC.lemma_17_merges_per_phase
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:17.91939+00:00
-- url     : https://prove2.me/theorems/e83d361c-4de8-4f58-be1d-9abcb334cf2e
-- title:
--   Lemma 17 — $x_0$'s cluster merges $\tilde O((k\cdot c)^{O(k)})$ times per phase
-- statement:
--   For all $\kappa,a>0$ and $c_\Delta\ge1$ there is a constant $C>0$ such that the following holds. Let $d$ be a well-behaved linkage on $P$ ($n=|P|$, dimension parameter $k\ge1$, triangle constant $c_\Delta$); fix a $c$-approximate HAC run ($c\ge1$), a point $x_0\in P$ and a phase $j$ with $\tilde\delta_j>0$. Then the number of merges $i\in I_j=[s_j,f_j]$ in which the cluster $X_i$ containing $x_0$ participates satisfies
--   $$\bigl|\{\,i\in[s_j,f_j] : X_i\in\{A_i,B_i\}\,\}\bigr|\le C\,(\log_2 n+1)^{C}\,(k\,c)^{C k}.$$
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: Õ((k · c)^{O(k)}) → C(log₂ n + 1)^C (k c)^{Ck} for a constant C chosen before the point type, the instance and the run; reason: pins the asymptotic notation with constants depending only on the fixed structural constants, as in the paper's proof
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
--   - encoding: val_j(A) = exp2(−d(X̃_j, A)/(4·δ̃_j)) divides by δ̃_j → hypothesis 0 < δ̃_j; reason: excludes only the cases in which val_j is undefined
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 17, p.22 (PDF p.25)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_rate
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_clusterOf
import Definitions.Def_ParallelHAC_HACRun_phaseEnd

namespace ParallelHAC

universe u

/-- **Lemma 17** (p.22): `x₀`'s cluster participates in at most `Õ((k·c)^{O(k)})` merges in each
phase. There is a constant `C`, depending only on `κ, a, cΔ`, such that for every well-behaved
linkage (dimension parameter `k ≥ 1`), every `c`-approximate HAC run (`c ≥ 1`), every `x₀ ∈ P`
and every phase `j`, the number of merges `i ∈ [s_j, f_j]` in which `X_i` participates is at most
`C (log₂ n + 1)^C (k c)^{C k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.2, Lemma 17, printed p.22 (PDF p.25).

**Formalization Note.** `C` is chosen before the point type, the instance and the run; `0 < δ̃_j`
is the nondegeneracy under which `val_j` (a division by `δ̃_j`) is defined. -/
theorem lemma_17_merges_per_phase :
    ∀ κ a cΔ : ℝ, 0 < κ → 0 < a → 1 ≤ cΔ → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (b c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ k → 1 ≤ c → WellBehaved P k κ a cΔ b d →
    ∀ (R : HACRun P d c) (x₀ : V), x₀ ∈ P →
    ∀ j : ℕ, R.IsPhase x₀ cΔ j → 0 < R.maxMergeValue (R.phaseStart x₀ cΔ j) →
      (((Finset.Icc (R.phaseStart x₀ cΔ j) (R.phaseEnd x₀ cΔ j)).filter
          (R.Participates x₀)).card : ℝ) ≤ rate C P.card k c := by sorry

end ParallelHAC
