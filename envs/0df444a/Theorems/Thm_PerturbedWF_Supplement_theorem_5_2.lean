-- Prove2me | Theorems.Thm_PerturbedWF_Supplement_theorem_5_2
-- name    : PerturbedWF.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:08:37.890374+00:00
-- url     : https://prove2.me/theorems/c680d3f5-e0b1-4dbf-97a7-44068bc00343
-- title:
--   Theorem 5.2: $k$-taxi on $\tau$-HSTs, $\sum_t\mathbb E\|X_{t-1}-Y_t\|\le\frac{16\tau m}{\tau-2}\mathrm{OPT}$, $m=O(\log n+D)$
-- statement:
--   There is an absolute constant $K>0$ with the following property. Let $\tau>2$ and let $([n],d)$ be the metric space of a $\tau$-HST of depth $D$. Then there are $m\le K(\log n+D)$ and vectors $A_i\in\mathbb R^m$, $z_i\in[-1,1]^m$ (one per leaf, pairwise distinct $A_i$) with
--   $$\|A_i-A_j\|_1\le d(i,j),\qquad \langle z_i,A_i-A_j\rangle\ge c_\tau\,d(i,j),\qquad c_\tau=\frac{\tau-2}{16\tau},$$
--   such that for every number of taxis $k$, every initial configuration $X_0$, every horizon $T$ and every request sequence $(r_1,s_1),\ldots,(r_T,s_T)$, every run of the $k$-taxi algorithm of §5.1 (sample $q$ uniformly from $[-1,1]^m$, $v=Aq$, $Y_t\in\arg\max_{y\ni r_t}\{\langle v,y\rangle-W_{t-1}(y)\}$, $X_t=Y_t+\delta_t$) satisfies
--   $$\sum_{t=1}^T\mathbb E\big[\|X_{t-1}-Y_t\|\big]\le\frac{m}{c_\tau}\,\mathrm{OPT}.$$
--   At depth $O(\log n)$ the algorithm is $O(\log n)$-competitive for $k$-taxi.
--
--   This is the $k$-taxi counterpart of the mission's goal (Theorem 4.3); on general metrics it yields $O(\log^2 n)$ through random tree embeddings.
--
--   **Formalization Note** The HST is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ`; $n$ is its number of leaves, $D$ its height, $\log$ natural. $m/c_\tau$ is written $16\tau m/(\tau-2)$.
--
--   Differences from the source:
--   - generalization: τ-HSTs of depth O(log n) (§5.1), ratio O(log n) → every depth D, with m ≤ K(log n + D); reason: at depth D ≤ c·log n this gives m = O(log n); same encoding as the published goal Theorem 4.3
--   - encoding: '≤ O(log n) OPT', with the proof's last line 'at most m/c_τ = O(log n)' → ≤ (16τ/(τ − 2))·m·OPT with m ≤ K(log n + D) and K > 0 absolute, quantified before τ and the tree; reason: the explicit ratio of the proof; the O(·) is uniform in the instance
--   - encoding: 'the vectors given by Theorem 3.4' → ∃ A, z with Theorem 3.4's properties 1 and 2, z_i ∈ [−1, 1]^m and A injective, chosen before the instance; reason: the algorithm depends only on the tree; injectivity follows from property 2
--   - encoding: E[·] over q uniform on [−1, 1]^m → lower Lebesgue integral ∫⁻ ENNReal.ofReal(·) under cubeLaw m; reason: the costs are nonnegative, so the lower integral is the expectation
--   - encoding: requests (r_t, s_t) ∈ [n] × [n] at times t ∈ [T] → two sequences r, s : ℕ → T.Leaf used at times 1, …, N; reason: index 0 is unused; r_t = s_t is allowed, as in the source
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 5.2, p.15 (PDF p.16), with the last line of its proof ('the competitive ratio is at most m/c_τ = O(log n)'), p.16 (PDF p.17); the algorithm of §5.1, p.15 (PDF p.16)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PerturbedWF_Supplement_KTaxi

namespace PerturbedWF.Supplement

open MeasureTheory

/-- **Theorem 5.2** (p.15, PDF p.16), with the last line of its proof ("the competitive ratio is
at most m/c_τ = O(log n)"), for the k-taxi algorithm of §5.1 (p.15) built from the vectors of
Theorem 3.4 (p.10). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work
Functions*, STOC 2027 submission (held version, sha256 e2e30a44…).

There is an absolute constant `K > 0` such that for every `τ > 2` and every weighted `τ`-HST `T`
with `n` leaves and depth `D` there are `m ≤ K (log n + D)` and vectors `A_i, z_i ∈ ℝ^m` with the
properties of Theorem 3.4 (`‖A_i − A_j‖₁ ≤ d(i, j)`, `z_i ∈ [−1, 1]^m`,
`⟨z_i, A_i − A_j⟩ ≥ c_τ d(i, j)`, `c_τ = (τ − 2)/(16τ)`; the `A_i` distinct) such that for every
number of taxis `k`, every initial configuration `X₀`, every horizon `N` and every request
sequence `(r_t, s_t)`, every run of the §5.1 algorithm satisfies
`∑_{t=1}^N E‖X_{t−1} − Y_t‖ ≤ (m / c_τ) · OPT`.

**Formalization Note.** The metric is the leaf metric `treeDist` of a `PolylogKServer.HST.WTree`
with `IsWeightedHST τ`; `n = |T.Leaf|`, `D = T.height`, `log` natural. `O(log n)` (at depth
`O(log n)`, §5.1) is kept explicit as `m / c_τ = 16τ m/(τ − 2)` with `m ≤ K (log n + D)`.
Expectations are lower integrals under the uniform law on `[−1, 1]^m`. -/
theorem theorem_5_2 :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 2 < τ →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : PolylogKServer.HST.WTree V),
      T.IsWeightedHST τ →
      ∃ m : ℕ, (m : ℝ) ≤ K * (Real.log (Fintype.card T.Leaf) + T.height) ∧
      ∃ A z : T.Leaf → Fin m → ℝ, Function.Injective A ∧ (∀ i l, |z i l| ≤ 1) ∧
        (∀ i j, ∑ l, |A i l - A j l| ≤ T.treeDist i.1 j.1) ∧
        (∀ i j, (τ - 2) / (16 * τ) * T.treeDist i.1 j.1 ≤ ∑ l, z i l * (A i l - A j l)) ∧
        ∀ (k : ℕ), ∀ X₀ ∈ kConfig T.Leaf k, ∀ (N : ℕ) (r s : ℕ → T.Leaf)
          (X Y : ℕ → (Fin m → ℝ) → (T.Leaf → ℝ)),
          IsKTaxiRun (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r s A N X Y →
          (∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal
              (transNorm (fun i j : T.Leaf => T.treeDist i.1 j.1) (X (t - 1) q - Y t q))
              ∂(cubeLaw m)) ≤
            ENNReal.ofReal (16 * τ / (τ - 2) * m *
              ktOPT (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r s N) := by sorry

end PerturbedWF.Supplement
