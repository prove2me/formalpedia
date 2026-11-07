-- Prove2me | Theorems.Thm_ParallelHAC_lemma_20_small_growth_small_drift
-- name    : ParallelHAC.lemma_20_small_growth_small_drift
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:19.970309+00:00
-- url     : https://prove2.me/theorems/04eeac97-975b-43a7-91fe-270b81e96ae5
-- title:
--   Lemma 20 — small growth means small drift
-- statement:
--   For all $\kappa,a>0$ and $c_\Delta\ge1$ there is a constant $C>0$ such that, with
--   $$\epsilon=\frac1{C\,(\log_2 n+1)^{C}\,(k\,c)^{C k}},$$
--   the following holds. Let $d$ be a well-behaved linkage on $P$ ($n=|P|$, dimension parameter $k\ge1$, triangle constant $c_\Delta$); fix a $c$-approximate HAC run ($c\ge1$), a point $x_0\in P$, a phase $j$ with $\tilde\delta_j>0$, and a merge $i$ in or immediately after the $j$-th phase ($s_j\le i\le f_j+1$, $i\le n-1$). If $X_i$ participates in the $i$-th merge, $\delta_i\le2\tilde\delta_j$ and $|X_i|\le(1+\epsilon)|\tilde X_j|$, then
--   $$d(\tilde X_j,\bar X_i)\le3c_\Delta\,\tilde\delta_j.$$
--
--   By contraposition, a phase that starts because of a large drift has multiplied the size of $x_0$'s cluster by $1+\epsilon$ (Lemma 21).
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - reading: ϵ = 1/Θ̃((k · c)^{O(k)}) 'for appropriately large hidden constants and exponents' → ∃ C (depending only on κ, a, cΔ) with ϵ = 1/(C(log₂ n + 1)^C (kc)^{Ck}); reason: the paper chooses the hidden constants large enough, uniformly over all phases (p.25); the conclusion is monotone in ϵ
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
--   - encoding: val_j(A) = exp2(−d(X̃_j, A)/(4·δ̃_j)) divides by δ̃_j → hypothesis 0 < δ̃_j; reason: excludes only the cases in which val_j is undefined
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 20, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_rate
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_mergeValue
import Definitions.Def_ParallelHAC_HACRun_clusterOf
import Definitions.Def_ParallelHAC_HACRun_phaseEnd

namespace ParallelHAC

universe u

/-- **Lemma 20** (p.24): small growth means small drift. There is a constant `C`, depending only on
`κ, a, cΔ`, such that with `ϵ := 1 / (C (log₂ n + 1)^C (k c)^{C k})` the following holds for every
well-behaved linkage (dimension parameter `k ≥ 1`), every `c`-approximate HAC run (`c ≥ 1`),
every `x₀ ∈ P`, every phase `j` and every merge `i` in or immediately after the `j`-th phase
(`s_j ≤ i ≤ f_j + 1`, `i ≤ n − 1`): if `X_i` participates in merge `i`, `δ_i ≤ 2 δ̃_j` and
`|X_i| ≤ (1 + ϵ)|X̃_j|`, then `d(X̃_j, X̄_i) ≤ 3 cΔ δ̃_j`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 20, printed p.24 (PDF p.27).

**Formalization Note.** The paper's `ϵ = 1/Θ̃((k·c)^{O(k)})` "for appropriately large hidden
constants and exponents" is read as: some `C` (independent of the instance) works; the conclusion
is monotone in `ϵ`. `0 < δ̃_j` is the nondegeneracy under which `val_j` (a division
by `δ̃_j`) is defined. -/
theorem lemma_20_small_growth_small_drift :
    ∀ κ a cΔ : ℝ, 0 < κ → 0 < a → 1 ≤ cΔ → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (b c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ k → 1 ≤ c → WellBehaved P k κ a cΔ b d →
    ∀ (R : HACRun P d c) (x₀ : V), x₀ ∈ P →
    ∀ j : ℕ, R.IsPhase x₀ cΔ j → 0 < R.maxMergeValue (R.phaseStart x₀ cΔ j) →
    ∀ i : ℕ, R.phaseStart x₀ cΔ j ≤ i → i ≤ R.phaseEnd x₀ cΔ j + 1 → i ≤ P.card - 1 →
      R.Participates x₀ i →
      R.mergeValue i ≤ 2 * R.maxMergeValue (R.phaseStart x₀ cΔ j) →
      ((R.clusterOf x₀ i).card : ℝ) ≤
        (1 + 1 / rate C P.card k c) * ((R.clusterOf x₀ (R.phaseStart x₀ cΔ j)).card : ℝ) →
      d (R.clusterOf x₀ (R.phaseStart x₀ cΔ j)) (R.partner x₀ i) ≤
        3 * cΔ * R.maxMergeValue (R.phaseStart x₀ cΔ j) := by sorry

end ParallelHAC
