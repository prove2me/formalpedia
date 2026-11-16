-- Prove2me | Theorems.Thm_PerturbedWF_Supplement_theorem_7_2
-- name    : PerturbedWF.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:09:15.877351+00:00
-- url     : https://prove2.me/theorems/a85dd3a3-fa47-4a26-bb8e-4170956dc9d1
-- title:
--   Theorem 7.2: metric bipartite matching on $\tau$-HSTs, $\sum_t\mathbb E[d(i_t,r_t)]\le\frac{16\tau m}{\tau-2}\mathrm{OPT}$
-- statement:
--   There is an absolute constant $K>0$ with the following property. Let $\tau>2$ and let $([n],d)$ be the metric space of a $\tau$-HST of depth $D$. Then there are $m\le K(\log n+D)$ and vectors $A_i\in\mathbb R^m$, $z_i\in[-1,1]^m$ with the properties of Theorem 3.4 ($\|A_i-A_j\|_1\le d(i,j)$, $\langle z_i,A_i-A_j\rangle\ge c_\tau d(i,j)$, $c_\tau=(\tau-2)/(16\tau)$) such that the following holds. Let the $k$ initial servers be placed by $X_0\in\{x\in\mathbb Z^n_{\ge0}:\sum_ix_i=k\}$ with at least one server at every point (so $n\le k$), and let $k$ requests $r_1,\ldots,r_k\in[n]$ arrive. Every run of the algorithm of §7.1 (sample $q$ uniformly from $[-1,1]^m$, $v=Aq$, $X_t\in\arg\max_x\{\langle v,x\rangle-W_t(x)\}$ with $X_t=X_{t-1}-e_{i_t}+e_{r_t}$, match $r_t$ to $i_t$) satisfies
--   $$\sum_{t=1}^k\mathbb E\big[d(i_t,r_t)\big]\le\frac{m}{c_\tau}\,\mathrm{OPT}.$$
--   At depth $O(\log n)=O(\log k)$ the algorithm is $O(\log k)$-competitive.
--
--   Combined with Lemma 7.1 and tree embeddings this recovers the known $O(\log^2k)$ bound for online metric bipartite matching.
--
--   **Formalization Note** The HST is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ`; the points are its leaves, which are the server locations. $I_t(q)$ is the location $i_t$.
--
--   Differences from the source:
--   - generalization: τ-HSTs of depth O(log n) = O(log k) (§7.1), ratio O(log k) → every depth D, with m ≤ K(log n + D); reason: n ≤ k, so at depth D ≤ c·log k this gives m = O(log k); same encoding as the published goal
--   - encoding: '≤ O(log k) OPT', with the proof's last line 'at most m/c_τ = O(log k)' → ≤ (16τ/(τ − 2))·m·OPT with m ≤ K(log n + D) and K > 0 absolute, quantified before τ and the tree; reason: the explicit ratio of the proof; the O(·) is uniform in the instance
--   - encoding: 'the vectors given by Theorem 3.4' → ∃ A, z with Theorem 3.4's properties 1 and 2, z_i ∈ [−1, 1]^m and A injective, chosen before the instance; reason: the algorithm depends only on the tree; injectivity follows from property 2
--   - encoding: E[·] over q uniform on [−1, 1]^m → lower Lebesgue integral ∫⁻ ENNReal.ofReal(·) under cubeLaw m; reason: the costs are nonnegative, so the lower integral is the expectation
--   - encoding: the reduced model: [n] = initial server locations, every r_t ∈ [n], exactly k requests → the points are the leaves of T, X₀ ∈ kConfig with X₀ i ≥ 1 for every leaf, requests r : ℕ → T.Leaf at times 1, …, k; reason: this is the model the theorem is stated for (§7, after Lemma 7.1)
--   - encoding: W_t(x) = ∞ off {x ≥ R_t}; OPT = min_x W_k(x) → mbWork in EReal (⊤ for ∞); mbOPT the real minimum of ‖X₀ − x‖ over {x ∈ C : x ≥ R_k}; reason: W_k is finite exactly there and R_k belongs to that set
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 7.2, p.19 (PDF p.20), with the last line of its proof ('the competitive ratio is at most m/c_τ = O(log k)'), p.20 (PDF p.21); the model of §7, pp.18–19, and the algorithm of §7.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_PolylogKServer_HST_Tree
import Definitions.Def_PerturbedWF_Supplement_Matching

namespace PerturbedWF.Supplement

open MeasureTheory

/-- **Theorem 7.2** (p.19, PDF p.20), with the last line of its proof ("the competitive ratio is
at most m/c_τ = O(log k)"), for the matching algorithm of §7.1 (p.19) built from the vectors of
Theorem 3.4 (p.10), in the reduced model of §7 (requests at the server locations).
C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…).

There is an absolute constant `K > 0` such that for every `τ > 2` and every weighted `τ`-HST `T`
with `n` leaves and depth `D` there are `m ≤ K (log n + D)` and vectors `A_i, z_i ∈ ℝ^m` with the
properties of Theorem 3.4 such that for every `k`, every initial server configuration
`X₀ ∈ kConfig` with at least one server at every leaf (so `n ≤ k`), and every sequence of `k`
requests at leaves, every run of the §7.1 algorithm satisfies
`∑_{t=1}^k E[d(i_t, r_t)] ≤ (m / c_τ) · OPT`, `c_τ = (τ − 2)/(16τ)`.

**Formalization Note.** As in Theorem 5.2: `treeDist` of a `WTree` with `IsWeightedHST τ`,
`n = |T.Leaf|`, `D = T.height`, `log` natural; `O(log k)` (at depth `O(log n) = O(log k)`) is kept
explicit as `16τ m/(τ − 2)` with `m ≤ K (log n + D) ≤ K (log k + D)`. `I t q` is the location
`i_t` of the server matched to `r_t`. Expectations are lower integrals under the uniform law on
`[−1, 1]^m`. -/
theorem theorem_7_2 :
    ∃ K : ℝ, 0 < K ∧ ∀ τ : ℝ, 2 < τ →
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : PolylogKServer.HST.WTree V),
      T.IsWeightedHST τ →
      ∃ m : ℕ, (m : ℝ) ≤ K * (Real.log (Fintype.card T.Leaf) + T.height) ∧
      ∃ A z : T.Leaf → Fin m → ℝ, Function.Injective A ∧ (∀ i l, |z i l| ≤ 1) ∧
        (∀ i j, ∑ l, |A i l - A j l| ≤ T.treeDist i.1 j.1) ∧
        (∀ i j, (τ - 2) / (16 * τ) * T.treeDist i.1 j.1 ≤ ∑ l, z i l * (A i l - A j l)) ∧
        ∀ (k : ℕ), ∀ X₀ ∈ kConfig T.Leaf k, (∀ i, 1 ≤ X₀ i) →
          ∀ (r : ℕ → T.Leaf) (X : ℕ → (Fin m → ℝ) → (T.Leaf → ℝ))
            (I : ℕ → (Fin m → ℝ) → T.Leaf),
          IsMatchRun (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r A X I →
          (∑ t ∈ Finset.Icc 1 k, ∫⁻ q, ENNReal.ofReal (T.treeDist (I t q).1 (r t).1)
              ∂(cubeLaw m)) ≤
            ENNReal.ofReal (16 * τ / (τ - 2) * m *
              mbOPT (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r) := by sorry

end PerturbedWF.Supplement
