-- Prove2me | Theorems.Thm_ParallelHAC_theorem_3_dendrogram_height
-- name    : ParallelHAC.theorem_3_dendrogram_height
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:27:56.769576+00:00
-- url     : https://prove2.me/theorems/43a83d22-7004-44ef-b9a7-c2f277a67252
-- title:
--   Theorem 3 — every $c$-approximate HAC with a well-behaved linkage has dendrogram height $\tilde O((k\cdot c)^{O(k)})$
-- statement:
--   For all structural constants $\kappa,a,b,\rho>0$ and $c_\Delta\ge1$ there is a constant $C_0>0$ such that the following holds. Let $P$ be a finite point set with $n=|P|$, let $k\ge1$ and $c\ge1$, and let $d$ be a linkage function that is well-behaved on $P$ — $\alpha$-packable with $\alpha=a(\log_2n+1)^a$ and exponent $\kappa k$, satisfying the approximate triangle inequality with constant $c_\Delta$, weight-stable, average-reducible, and with poly-bounded diameter $b\,n^b$ — and whose aspect ratio is at most $\rho n^\rho$. Then every $c$-approximate HAC run on $(P,d)$, however ties are broken, produces a dendrogram of height
--   $$\mathrm{height}\le C_0\,(\log_2 n+1)^{C_0}\,(k\,c)^{C_0 k}.$$
--
--   For centroid and Ward's linkage (which are well-behaved, Theorems 1–2 of the paper) this gives polylogarithmic height when $k=O(\log\log n/\log\log\log n)$ and $c=O(1)$, the structural fact behind the paper's parallel HAC algorithms.
--
--   **Formalization Note** The constant $C_0$ is chosen before the point type, the point set, the linkage and the run, so it depends only on $\kappa,a,b,\rho,c_\Delta$ and not on $k$, $c$, $n$ or $d$.
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
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.2, Theorem 3, p.7 (PDF p.10); restated p.18 (PDF p.21) and p.25 (PDF p.28); proof §4, pp.18–25

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_AspectRatioLE
import Definitions.Def_ParallelHAC_rate
import Definitions.Def_ParallelHAC_HACRun
import Definitions.Def_ParallelHAC_HACRun_height

namespace ParallelHAC

universe u

/-- **Theorem 3** (p.7): every `c`-approximate HAC for a well-behaved linkage function with
`poly(n)` aspect ratio has a dendrogram of height `Õ((k·c)^{O(k)})` in `ℝ^k`.

For all structural constants `κ, a, b, ρ > 0` and `cΔ ≥ 1` there is `C₀ > 0` such that: for every
point type `V`, finite point set `P ⊆ V` with `n = |P|`, dimension parameter `k ≥ 1`,
approximation factor `c ≥ 1` and linkage `d` that is well-behaved on `P` (packability
`α = a(log₂ n + 1)^a`, exponent `κ k`; triangle constant `cΔ`; diameter polynomial `b n^b`) with
aspect ratio at most `ρ n^ρ`, every `c`-approximate HAC run on `(P, d)`, under any tie-breaking,
has dendrogram height at most `C₀ (log₂ n + 1)^{C₀} (k c)^{C₀ k}`.
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.2, Theorem 3, printed p.7 (PDF p.10); restated
p.18 and p.25; proof §4, pp.18–25.

**Formalization Note.** The paper's `ℝ^k` is the instance `V = EuclideanSpace ℝ (Fin k)`; the
statement is for any point type, since the definitions use only linkage values. `C₀` is chosen
before the point type, the instance and the run, so it is independent of `k, c, n, d`. -/
theorem theorem_3_dendrogram_height :
    ∀ κ a b ρ cΔ : ℝ, 0 < κ → 0 < a → 0 < b → 0 < ρ → 1 ≤ cΔ → ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ {V : Type u} [DecidableEq V] (P : Finset V) (k : ℕ) (c : ℝ)
      (d : Finset V → Finset V → ℝ), 1 ≤ k → 1 ≤ c → WellBehaved P k κ a cΔ b d →
      AspectRatioLE P d ρ →
    ∀ R : HACRun P d c, (R.height : ℝ) ≤ rate C₀ P.card k c := by sorry

end ParallelHAC
