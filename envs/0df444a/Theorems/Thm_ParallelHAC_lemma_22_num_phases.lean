-- Prove2me | Theorems.Thm_ParallelHAC_lemma_22_num_phases
-- name    : ParallelHAC.lemma_22_num_phases
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:26.32113+00:00
-- url     : https://prove2.me/theorems/296164c8-2f61-4898-9325-c47dab7852ea
-- title:
--   Lemma 22 — $\tilde O((k\cdot c)^{O(k)})$ phases in total
-- statement:
--   For all $\kappa,a,b,\rho>0$ and $c_\Delta\ge1$ there is a constant $C>0$ such that the following holds. Let $d$ be a well-behaved linkage on $P$ ($n=|P|$, dimension parameter $k\ge1$) with aspect ratio at most $\rho n^\rho$; fix a $c$-approximate HAC run ($c\ge1$) and a point $x_0\in P$. Then the number $J$ of phases satisfies
--   $$J\le C\,(\log_2 n+1)^{C}\,(k\,c)^{C k}.$$
--
--   Differences from the source:
--   - generalization: points P ⊆ ℝ^k → P a finite set in an arbitrary type V, with k the dimension parameter of the packing bound; reason: Definitions 1–5 and the proof use only linkage values (p.5: low dimension enters only through packing); V = EuclideanSpace ℝ (Fin k) is the paper's case
--   - generalization: the axioms of Definitions 1–5 hold for all subsets of ℝ^k (packing for every family C ⊆ 2^{ℝ^k}) → they are required only for nonempty subsets of P, packing only for pairwise disjoint families of them, and poly-bounded diameter only for P itself; reason: a weaker hypothesis that every well-behaved linkage in the paper's sense satisfies; the proof only applies the axioms to clusters of the run (Lemma 16 packs part of a clustering)
--   - encoding: α = Õ(1), exponent O(k), poly(|P|) in Definitions 1, 5 → α = a(log₂ n + 1)^a, exponent κk, b·n^b with κ, a, b fixed before the instance; reason: pins the paper's asymptotic notation (footnotes 3 and 5: Õ hides poly(log n) factors, poly(n) ≤ O(n^c))
--   - encoding: Õ((k · c)^{O(k)}) → C(log₂ n + 1)^C (k c)^{Ck} for a constant C chosen before the point type, the instance and the run; reason: pins the asymptotic notation with constants depending only on the fixed structural constants, as in the paper's proof
--   - encoding: a c-approximate HAC (any tie-breaking), merges i = 1, …, n − 1, clusterings C_i → a HACRun: merge pairs A i, B i, i ∈ [1, n−1], of distinct members of C_i (computed from the merges, starting from singletons) with d(A_i,B_i) ≤ c·d(C,D) for all distinct C, D ∈ C_i; reason: same instances; quantifying over every HACRun is 'regardless of how ties are broken' (p.7)
--   - encoding: c_∆ the triangle constant → hypothesis 1 ≤ cΔ; reason: p.19: 'Taking c∆ ≥ 1, as we may'; a linkage satisfying Definition 2 with a smaller constant satisfies it with constant 1
--   - reading: aspect ratio max_{u,v∈P} d(u,v) / min_{u,v∈P} d(u,v) ≤ poly(n) → all singleton distances between distinct points are positive and d(u,v) ≤ ρ n^ρ d(w,x) for distinct u ≠ v, w ≠ x; reason: at u = v the ratio is undefined (d(u,u) = 0 for the paper's linkages), so the extrema range over distinct pairs; a finite ratio needs a positive minimum; poly(n) pinned as ρ n^ρ
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 22, p.25 (PDF p.28)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_AspectRatioLE
import Definitions.Def_ParallelHAC_rate
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_phaseEnd

namespace ParallelHAC

universe u

/-- **Lemma 22** (p.25): the number of phases is at most `Õ((k·c)^{O(k)})` assuming polynomial
aspect ratio. There is a constant `C`, depending only on `κ, a, b, ρ, cΔ`, such that for every
well-behaved linkage (dimension parameter `k ≥ 1`) with aspect ratio at most `ρ n^ρ`, every
`c`-approximate HAC run (`c ≥ 1`) and every `x₀ ∈ P`, the number of phases is at most
`C (log₂ n + 1)^C (k c)^{C k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §4.3, Lemma 22, printed p.25 (PDF p.28).

**Formalization Note.** `C` is chosen before the point type, the instance and the run. -/
theorem lemma_22_num_phases :
    ∀ κ a b ρ cΔ : ℝ, 0 < κ → 0 < a → 0 < b → 0 < ρ → 1 ≤ cΔ → ∃ C : ℝ, 0 < C ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ k → 1 ≤ c → WellBehaved P k κ a cΔ b d →
      AspectRatioLE P d ρ →
    ∀ (R : HACRun P d c) (x₀ : V), x₀ ∈ P →
      (R.numPhases x₀ cΔ : ℝ) ≤ rate C P.card k c := by sorry

end ParallelHAC
