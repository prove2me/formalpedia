-- Prove2me | Theorems.Thm_PerturbedWF_theorem_4_3
-- name    : PerturbedWF.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:47:05.882364+00:00
-- url     : https://prove2.me/theorems/87ff826a-ca85-44c6-8383-e88712374c02
-- title:
--   Theorem 4.3: metric allocation on $\tau$-HSTs, movement $\le\frac{16\tau m}{\tau-2}\mathrm{OPT}$ and total cost $\le(1+\frac{16\tau m}{\tau-2})\mathrm{OPT}$, $m=O(\log n+D)$
-- statement:
--   There is an absolute constant $K>0$ with the following property. Let $\tau>2$ and let $([n],d)$ be the metric space of a $\tau$-HST of depth $D$ (the leaves of a rooted tree with edge weights $w_f\le w_e/\tau$ for consecutive edges, $d$ the weighted path length). Then there are $m\le K(\log n+D)$ and vectors $A_i\in\mathbb R^m$, $z_i\in[-1,1]^m$ (one per leaf, as in Theorem 3.4), pairwise distinct with
--   $$\|A_i-A_j\|_1\le d(i,j),\qquad\langle z_i,A_i-A_j\rangle\ge c_\tau\,d(i,j),\qquad c_\tau=\frac{\tau-2}{16\tau},$$
--   such that the following holds. For every initial configuration $x_0$ in the simplex, every horizon $T$, and every sequence of metric-allocation requests $F_t(x)=f_t(x_{r_t})$ ($f_t:[0,1]\to\mathbb R_{\ge0}$ convex, continuous, monotone, the direction possibly changing with $t$), every run $X_0=x_0,X_1,\dots,X_T$ of the algorithm that samples $q$ uniformly from $[-1,1]^m$, sets $v=Aq$ and moves to a maximizer $X_t$ of $\langle v,x\rangle-W_t(x)$ satisfies
--   $$\sum_{t=1}^T\mathbb E\big[\|X_{t-1}-X_t\|\big]\le\frac{m}{c_\tau}\,\mathrm{OPT}$$
--   and
--   $$\sum_{t=1}^T\mathbb E\big[\|X_{t-1}-X_t\|+F_t(X_t)\big]\le\Big(1+\frac{m}{c_\tau}\Big)\mathrm{OPT}.$$
--   At depth $D=O(\log n)$ the algorithm is $O(\log n)$-competitive.
--
--   This is the paper's headline result for metric allocation; it improves the previous $O(n)$ bound exponentially, and on general metrics it gives $O(\log^2n)$ through random tree embeddings.
--
--   **Formalization Note.** The HST is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ`, $n$ its number of leaves, $D$ its height, $\log$ natural. $m/c_\tau$ is written $16\tau m/(\tau-2)$. Expectations are lower integrals of the nonnegative costs under the uniform law on the cube.
--
--   Differences from the source:
--   - generalization: τ-HSTs of depth O(log n) (§4.1), ratio O(log n) → every depth D, with m ≤ K(log n + D); reason: at depth D ≤ c·log n this gives m = O(log n); the paper notes its results extend to arbitrary HSTs (p.10)
--   - generalization: X_t ∈ argmax over supp(W_t) (§4.1) → X_t any maximizer of ⟨Aq, ·⟩ − W_t over the whole simplex (IsAlgRun); reason: by Lemma 2.3 every maximizer over supp(W_t) is a maximizer over C, so every run of §4.1 is covered
--   - encoding: '≤ O(log n) OPT', with the proof's 'at most m/c_τ = O(log n)' → ≤ (16τ/(τ − 2))·m·OPT with m ≤ K(log n + D) and K > 0 absolute, quantified before τ and the tree; reason: the explicit ratio of the proof; the O(·) is uniform in the instance
--   - encoding: 'let A_i ∈ ℝ^m and z_i ∈ ℝ^m … be the vectors given by Theorem 3.4' → ∃ A, z with Theorem 3.4's properties 1 and 2, z_i ∈ [−1, 1]^m and A injective, chosen before x₀, the horizon and the requests; reason: the algorithm depends only on the tree; injectivity is implied by property 2 and is the hypothesis of Lemma 2.4
--   - encoding: 'By Lemma 4.2, this implies that the algorithm is O(log n)-competitive' → the total-cost bound Σ E[‖X_{t−1} − X_t‖ + F_t(X_t)] ≤ (1 + 16τm/(τ − 2))·OPT; reason: the movement bound plus Lemma 4.2 give exactly this ratio
--   - encoding: expectation E[·] over q uniform on [−1, 1]^m → lower Lebesgue integral ∫⁻ ENNReal.ofReal(·) under cubeLaw m; reason: the costs are nonnegative, so the lower integral is the expectation; no integrability or measurability of the run is needed
--   - encoding: requests F_t(x) = f_t(x_{r_t}) with f_t convex, monotone and continuous (after the [BC22] reduction, footnote 1) → sequences r, f with IsMAReq (f t) for 1 ≤ t ≤ N: convex, continuous, monotone in either direction, nonnegative on [0, 1]; reason: this is the request class the paper analyzes (p.12, 'We thus design and analyze our algorithm for this version')
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 4.3 and the sentence after it, p.13 (PDF p.14), with the last line of its proof ('the competitive ratio of the movement cost is at most m/c_τ = O(log n)'); the algorithm of §4.1, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PerturbedWF_Algorithm

namespace PerturbedWF

open MeasureTheory

/-- **Theorem 4.3** (p.13, PDF p.14), with the sentence after it ("By Lemma 4.2, this implies that
the algorithm is O(log n)-competitive") and the last line of its proof ("the competitive ratio of
the movement cost is at most m/c_τ = O(log n)"), for the algorithm of §4.1 (p.12) built from the
vectors of Theorem 3.4 (p.10). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…)

There is an absolute constant `K > 0` such that for every `τ > 2` and every weighted `τ`-HST `T`
with `n` leaves and depth `D` there are a dimension `m ≤ K (log n + D)` and vectors
`A_i, z_i ∈ ℝ^m` with the properties of Theorem 3.4 (`‖A_i − A_j‖₁ ≤ d(i, j)`, `z_i ∈ [−1, 1]^m`,
`⟨z_i, A_i − A_j⟩ ≥ c_τ d(i, j)`, `c_τ = (τ − 2)/(16τ)`; in particular the `A_i` are distinct)
such that, for every initial configuration `x₀`, every horizon `N` and every sequence of
metric-allocation requests, every run of the algorithm with `v = Aq` satisfies

* (movement) `∑_{t=1}^N E‖X_{t−1} − X_t‖ ≤ (m / c_τ) · OPT`, and
* (total cost) `∑_{t=1}^N E[‖X_{t−1} − X_t‖ + f_t(X_t(r_t))] ≤ (1 + m / c_τ) · OPT`.

**Formalization Note.**
* The metric is the leaf metric `treeDist` of a `PolylogKServer.HST.WTree` with
  `IsWeightedHST τ` (an edge is identified with its lower node); `n = |T.Leaf|`, `D = T.height`.
  §4.1 assumes depth `O(log n)`; the statement holds for every depth with `m ≤ K (log n + D)`,
  which gives `m = O(log n)` at depth `O(log n)`. `O(log n)` is kept explicit as
  `m / c_τ = 16τ m / (τ − 2)`; `K` is quantified before `τ` and the tree. `log` is natural.
* Expectations are lower Lebesgue integrals `∫⁻ ENNReal.ofReal (·)` of the (nonnegative) costs
  under the uniform law on `[−1, 1]^m`; no integrability or measurability of the run is assumed.
* Every run (`IsAlgRun`): `X_0 = x₀` and `X_t` any maximizer of `⟨Aq, ·⟩ − W_t` over the simplex
  (a superset of the maximizers over `supp(W_t)` used in §4.1).
* Requests are the reduced class of §4 (`F_t(x) = f_t(x_{r_t})`, `f_t` convex, continuous,
  monotone in either direction, nonnegative on `[0, 1]`). -/
theorem theorem_4_3 :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 2 < τ →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : PolylogKServer.HST.WTree V),
      T.IsWeightedHST τ →
      ∃ m : ℕ, (m : ℝ) ≤ K * (Real.log (Fintype.card T.Leaf) + T.height) ∧
      ∃ A z : T.Leaf → Fin m → ℝ, Function.Injective A ∧ (∀ i k, |z i k| ≤ 1) ∧
        (∀ i j, ∑ k, |A i k - A j k| ≤ T.treeDist i.1 j.1) ∧
        (∀ i j, (τ - 2) / (16 * τ) * T.treeDist i.1 j.1 ≤ ∑ k, z i k * (A i k - A j k)) ∧
        ∀ x₀ ∈ simplex T.Leaf, ∀ (N : ℕ) (r : ℕ → T.Leaf) (f : ℕ → ℝ → ℝ),
          (∀ t ∈ Finset.Icc 1 N, IsMAReq (f t)) →
          ∀ X : ℕ → (Fin m → ℝ) → (T.Leaf → ℝ),
            IsAlgRun (fun i j : T.Leaf => T.treeDist i.1 j.1) x₀ (maCost r f) A N X →
            (∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal
                (transNorm (fun i j : T.Leaf => T.treeDist i.1 j.1) (X (t - 1) q - X t q))
                ∂(cubeLaw m)) ≤
              ENNReal.ofReal (16 * τ / (τ - 2) * m *
                OPT (fun i j : T.Leaf => T.treeDist i.1 j.1) x₀ (maCost r f) N) ∧
            (∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal
                (transNorm (fun i j : T.Leaf => T.treeDist i.1 j.1) (X (t - 1) q - X t q) +
                  f t (X t q (r t))) ∂(cubeLaw m)) ≤
              ENNReal.ofReal ((1 + 16 * τ / (τ - 2) * m) *
                OPT (fun i j : T.Leaf => T.treeDist i.1 j.1) x₀ (maCost r f) N) := by sorry

end PerturbedWF
