-- Prove2me | Theorems.Thm_PerturbedWF_Supplement_theorem_8_9
-- name    : PerturbedWF.Supplement.theorem_8_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:11:25.668203+00:00
-- url     : https://prove2.me/theorems/692c6311-8c57-4f79-a97d-2fafe31de06b
-- title:
--   Theorem 8.9: the perturbed work function algorithm is $O(\log^2k)$-competitive for $k$-server on HSTs
-- statement:
--   Let $\tau>1$. There is $c>0$, depending only on $\tau$, with the following property. Let $T$ be a $\tau$-HST whose edges incident to a common parent node have a common weight, with leaves $[n]$ and tree distance $d$. For every number of servers $k$ and every initial configuration $X_0\in\{x\in\mathbb Z^n_{\ge0}:\sum_ix_i=k\}$ there is $C$, independent of the request sequence, such that every run of the algorithm of §8.3.1 (each $q_e$, $e\in E$, drawn independently with the density (8.2) for $\kappa=k^3$; $v_i=\sum_{e\in P_i}w_eq_e$; $X_t\in\arg\max_{x\ni r_t}\{\langle v,x\rangle-W_{t-1}(x)\}$) satisfies, for every request sequence $r_1,\ldots,r_T$,
--   $$\sum_{t=1}^T\mathbb E\big[\|X_t-X_{t-1}\|\big]\le c\,\log^2(k+1)\cdot\mathrm{OPT}+C.$$
--   That is, the algorithm is $O(\log^2k)$-competitive for $k$-server on HSTs.
--
--   Through tree embeddings this gives an $O(\log^2k\log n)$-competitive algorithm for $k$-server on $n$-point metrics, recovering a known bound with a simple randomized-perturbation algorithm.
--
--   **Formalization Note** The HST is a `PolylogKServer.HST.WTree` with `IsWeightedHST τ`; edges are the non-root nodes. OPT is the minimum of the work function (8.1). Expectations are lower integrals under the product law with density (8.2) on $[-1,1]^E$.
--
--   Differences from the source:
--   - reading: 'O(log² k)-competitive for k-server on HSTs' (τ > 1, §8.3) → ∀ τ > 1, ∃ c > 0 such that for every such HST, every k and X₀ there is C independent of the requests with Σ E‖X_t − X_{t−1}‖ ≤ c·log²(k+1)·OPT + C; reason: the proof's constants C₁ = 4τ/((τ−1)ln 2) and K = 1 + 2ρ(1)/(τ−1) depend on τ and blow up as τ → 1; the additive constants of Lemmas 8.5 and 8.8 depend on the tree, k and X₀, not on the requests
--   - encoding: log² k → log²(k + 1); reason: equal up to a factor at most 4 for k ≥ 2, and meaningful at k = 1
--   - encoding: 'all edges incident to the same parent node have the same weight' → SiblingsEqual T: parent u = parent v → W u = W v for non-root u, v; reason: edges are identified with their lower nodes
--   - encoding: the algorithm (any X_t ∈ argmax), E over q_e i.i.d. with density (8.2) → every run (IsKServerRun) and the lower integral under expLaw (Edge T) (k³); reason: all selections agree almost surely; the costs are nonnegative
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), Theorem 8.9, p.29 (PDF p.30); the HST assumption of §8.3, p.24 (PDF p.25); the algorithm of §8.3.1, p.25 (PDF p.26)

import Mathlib
import Definitions.Def_PerturbedWF_Supplement_HSTKServer

namespace PerturbedWF.Supplement

open MeasureTheory

/-- **Theorem 8.9** (p.29, PDF p.30), for the k-server algorithm of §8.3.1 (p.25) on the HSTs of
§8.3 (p.24). C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work
Functions*, STOC 2027 submission (held version, sha256 e2e30a44…).

The algorithm is `O(log² k)`-competitive for k-server on HSTs: for every `τ > 1` there is `c > 0`
such that for every weighted `τ`-HST `T` whose edges below a common parent have a common weight,
every number of servers `k` and every initial configuration `X₀` there is `C`, independent of the
request sequence, such that every run of the algorithm (`q_e` i.i.d. with density (8.2),
`κ = k³`, `v_i = ∑_{e ∈ P_i} w_e q_e`) on every request sequence satisfies
`∑_{t=1}^N E‖X_t − X_{t−1}‖ ≤ c · log²(k + 1) · OPT + C`.

**Formalization Note.** `c` depends on `τ` only (not on `k`, the tree or `X₀`); `log²(k + 1)` is
`log² k` up to a constant for `k ≥ 2` and keeps `k = 1` meaningful. The metric is `treeDist`
on the leaves; edges are the non-root nodes (`Edge T`); `A = hstMatrix T`; `OPT` is the minimum
of the work function (8.1). Expectations are lower integrals under `expLaw (Edge T) (k³)`. -/
theorem theorem_8_9 :
    ∀ τ : ℝ, 1 < τ → ∃ c : ℝ, 0 < c ∧
    ∀ {V : Type} [Fintype V] [DecidableEq V] (T : PolylogKServer.HST.WTree V),
      T.IsWeightedHST τ → SiblingsEqual T →
      ∀ (k : ℕ), ∀ X₀ ∈ kConfig T.Leaf k, ∃ C : ℝ,
        ∀ (N : ℕ) (r : ℕ → T.Leaf) (X : ℕ → (Edge T → ℝ) → (T.Leaf → ℝ)),
          IsKServerRun (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r (hstMatrix T) N X →
          (∑ t ∈ Finset.Icc 1 N, ∫⁻ q, ENNReal.ofReal
              (transNorm (fun i j : T.Leaf => T.treeDist i.1 j.1) (X t q - X (t - 1) q))
              ∂(expLaw (Edge T) ((k : ℝ) ^ 3))) ≤
            ENNReal.ofReal (c * Real.log ((k : ℝ) + 1) ^ 2 *
              ksOPT (fun i j : T.Leaf => T.treeDist i.1 j.1) k X₀ r N + C) := by sorry

end PerturbedWF.Supplement
