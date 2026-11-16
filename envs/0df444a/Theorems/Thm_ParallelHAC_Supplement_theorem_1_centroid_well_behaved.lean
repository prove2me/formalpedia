-- Prove2me | Theorems.Thm_ParallelHAC_Supplement_theorem_1_centroid_well_behaved
-- name    : ParallelHAC.Supplement.theorem_1_centroid_well_behaved
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:33:35.927203+00:00
-- url     : https://prove2.me/theorems/dc44f45e-2801-4d12-8488-f6ca8b8464c1
-- title:
--   Theorem 1 — the centroid linkage is well-behaved
-- statement:
--   There are constants $\kappa>0$, $a>0$, $c_\Delta\ge1$ and $b>0$ such that for every dimension $k$ and every finite point set $P\subseteq\mathbb R^k$ the centroid linkage $d_{\mathrm{cen}}(A,B)=\|\mu(A)-\mu(B)\|$ is well-behaved on $P$ (Definition 6):
--   1. it is nonnegative and symmetric on nonempty clusters of $P$;
--   2. it is $\alpha$-packable (Definition 1) with $\alpha=a(\log_2|P|+1)^a$ and exponent $\kappa k$, for every family of nonempty clusters of $P$, disjoint or not;
--   3. it satisfies the approximate triangle inequality (Definition 2) with constant $c_\Delta$;
--   4. it is weight-stable (Definition 3) and average-reducible (Definition 4);
--   5. it has poly-bounded diameter (Definition 5) with polynomial $b|P|^b$.
--
--   Together with Theorem 3 this gives the dendrogram height bound $\tilde O(k^{O(k)})$ for every $c$-approximate centroid HAC with poly($n$) aspect ratio, $c=O(1)$.
--
--   **Formalization Note** The conclusion is the base mission's `ParallelHAC.WellBehaved P k κ a cΔ b d_cen` together with `PackableAll` (packing for non-disjoint families), with the constants chosen before $k$ and $P$.
--
--   Differences from the source:
--   - encoding: 'well-behaved' with α = Õ(1), packing exponent O(k), a fixed constant c∆ and poly(|P|) (Definitions 1, 2, 5, 6) → ∃ κ a cΔ b with 0 < κ, 0 < a, 1 ≤ cΔ, 0 < b, chosen before k and P; α = a(log₂|P| + 1)^a, exponent κk, polynomial b|P|^b (the base mission's ParallelHAC.WellBehaved); reason: pins the asymptotic notation exactly as the published goal Theorem 3 reads it, so the conclusion is its hypothesis; cΔ ≥ 1 is allowed by p.19 ('Taking c∆ ≥ 1, as we may'): a constant that works can be raised to 1
--   - reading: Definitions 1–5 for all A, B, C ⊆ ℝ^k (packing: every family 𝒞 ⊆ 2^{ℝ^k}); α and poly(|P|) in terms of the instance size n → for every k and every finite P ⊆ EuclideanSpace ℝ (Fin k), the axioms for all nonempty clusters A, B, C ⊆ P and all finite families of nonempty clusters of P, with n = |P|; reason: α = Õ(1) and poly(|P|) only make sense relative to an instance; P is arbitrary, so the triangle, weight-stability and average-reducibility clauses for any finite nonempty A, B, C ⊆ ℝ^k follow with P = A ∪ B ∪ C; clusters are nonempty (the centroid of ∅ is undefined)
--   - encoding: Definition 1 packs every family of clusters → ParallelHAC.WellBehaved (whose packing clause is for pairwise disjoint families) together with PackableAll (every family, disjoint or not); reason: the published WellBehaved weakens packing to disjoint families as a hypothesis; the extra conjunct restores Definition 1 as printed, so the conclusion is the paper's
-- source:
--   Bateni, Dhulipala, Fletcher, Gowda, Hershkowitz, Jayaram, Łącki, Parallel Hierarchical Agglomerative Clustering in Low Dimensions, arXiv:2507.20047 (sha256 a21061c8…), §2.1, Theorem 1, p.6 (PDF p.9); restated p.14 (PDF p.17), proof Lemmas 1–5, pp.14–15 (PDF pp.17–18)

import Mathlib
import Definitions.Def_ParallelHAC_WellBehaved
import Definitions.Def_ParallelHAC_Supplement_centroidLinkage
import Definitions.Def_ParallelHAC_Supplement_PackableAll

namespace ParallelHAC.Supplement

/-- **Theorem 1** (p.6): the centroid linkage `d_cen` is well-behaved (Definition 6).

There are constants `κ > 0`, `a > 0`, `cΔ ≥ 1`, `b > 0` such that for every dimension `k` and
every finite point set `P ⊆ ℝ^k`, `d_cen` is well-behaved on `P` in the sense of the base mission's
`ParallelHAC.WellBehaved` (packability with `α = a (log₂ |P| + 1)^a` and exponent `κ k`, triangle
constant `cΔ`, weight-stability, average-reducibility, poly-bounded diameter with `b |P|^b`), and
moreover packs every family of clusters of `P`, disjoint or not (`PackableAll`, Definition 1 as
printed).
Source: arXiv:2507.20047 (sha256 a21061c8…), §2.1, Theorem 1, printed p.6 (PDF p.9); restated
p.14 (PDF p.17), proof Lemmas 1–5, pp.14–15.

**Formalization Note.** The constants are chosen before `k` and `P` ("fixed", Definitions 2 and
6); `cΔ ≥ 1` and positivity are the forms the base Theorem 3 uses. -/
theorem theorem_1_centroid_well_behaved :
    ∃ κ a cΔ b : ℝ, 0 < κ ∧ 0 < a ∧ 1 ≤ cΔ ∧ 0 < b ∧
      ∀ (k : ℕ) (P : Finset (EuclideanSpace ℝ (Fin k))),
        ParallelHAC.WellBehaved P k κ a cΔ b (centroidLinkage k) ∧
          PackableAll P k κ a (centroidLinkage k) := by sorry

end ParallelHAC.Supplement
